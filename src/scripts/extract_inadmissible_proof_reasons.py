#!/usr/bin/env python3
"""Extract inadmissible existential witness reasons from llm_baseline outputs."""

import argparse
import json
import os
import re
import sys
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Sequence, Set


REPO_ROOT = Path(__file__).resolve().parents[2]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.goedel.repl_scheduler import DEFAULT_IMPORTS, scheduler


def add_lean_import(imports: str, module: str) -> str:
    lines = imports.splitlines()
    import_line = f"import {module}"
    if import_line in [line.strip() for line in lines]:
        return imports
    insert_at = 0
    while insert_at < len(lines) and lines[insert_at].strip().startswith("import "):
        insert_at += 1
    lines.insert(insert_at, import_line)
    return "\n".join(lines).rstrip() + "\n"


IMPORTS = add_lean_import(DEFAULT_IMPORTS, "utils.extract_exists_witness")


REASON_COMMAND = r'''
open Lean Elab Command Meta

namespace ECP.InadmissibleReason

syntax inadmissible_reason_opts :=
  "with"
  "admissible_vocabulary" ":=" term
  ("allow_quantifier" ":=" term)?

private partial def collectQuotedNamesForReason (stx : Syntax) : CommandElabM (List Name) := do
  if stx.getKind == `Lean.Parser.Term.doubleQuotedName then
    if stx.getNumArgs == 3 && stx[2].isIdent then
      return [stx[2].getId]
    else
      throwErrorAt stx "expected a quoted constant name"
  let mut names := []
  for child in stx.getArgs do
    names := names ++ (← collectQuotedNamesForReason child)
  return names

private def parseBoolLiteralForReason (stx : Syntax) : CommandElabM Bool := do
  match stx with
  | `(term| true) => return true
  | `(term| false) => return false
  | _ => throwErrorAt stx "expected boolean literal `true` or `false`"

private def parseReasonOptions (stx : Syntax) :
    CommandElabM (List Name × Canonical.StructuralOptions) := do
  match stx with
  | `(inadmissible_reason_opts|
      with admissible_vocabulary := $vocab
      $[allow_quantifier := $allowQuantifier]?) =>
      let names ← collectQuotedNamesForReason vocab.raw
      let allowQuantifierValue ←
        match allowQuantifier with
        | some stx => parseBoolLiteralForReason stx
        | none => pure true
      let opts : Canonical.StructuralOptions := {
        allowQuantifier := allowQuantifierValue
      }
      return (names, opts)
  | _ =>
      throwErrorAt stx
        "malformed options. Expected: `with admissible_vocabulary := [...]`"

private def ppQuotedNameForReason (n : Name) : String :=
  "``" ++ n.toString

syntax (name := extractFirstExistsWitnessReasonCmd)
  "#extract_first_exists_witness_reason" ident inadmissible_reason_opts : command

@[command_elab extractFirstExistsWitnessReasonCmd]
def elabExtractFirstExistsWitnessReasonCmd : CommandElab := fun stx => do
  let idStx := stx[1]
  let optStx := stx[2]
  let (allowedNames, structuralOpts) ← parseReasonOptions optStx
  let allowed := Std.HashSet.ofList allowedNames
  let name ← Command.liftTermElabM <| realizeGlobalConstNoOverloadWithInfo idStx
  let ci ← getConstInfo name
  let some value := ci.value?
    | throwError "{name} has no body to inspect"
  let some witness ← Command.liftTermElabM <| ECP.ExtractExistsWitness.firstWitnessAtProofRoot? value
    | throwError "could not find an outer proof-root Exists.intro in {name}"
  let fmt ← Command.liftTermElabM <| Meta.ppExpr witness
  logInfo m!"```\n{fmt}\n```"
  let ok ← Command.liftTermElabM <| Canonical.isCanonicalExprMWithStructural allowed structuralOpts witness
  if ok then
    logInfo "```canonical```"
  else
    logInfo "```not canonical```"
  let cs ← Command.liftTermElabM <| Canonical.collectRelevantConsts witness
  let shown := cs.toList.map ppQuotedNameForReason
  logInfo m!"```[{String.intercalate ", " shown}]```"

end ECP.InadmissibleReason
'''


IMPORTS_WITH_REASON_COMMAND = IMPORTS.rstrip() + "\n" + REASON_COMMAND + "\n"


def read_jsonl(path: Path) -> List[Dict[str, Any]]:
    rows: List[Dict[str, Any]] = []
    if not path.exists():
        return rows
    with path.open("r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if line:
                row = json.loads(line)
                if isinstance(row, dict):
                    rows.append(row)
    return rows


def write_jsonl(path: Path, rows: Iterable[Dict[str, Any]]) -> None:
    with path.open("w", encoding="utf-8") as f:
        for row in rows:
            f.write(json.dumps(row, ensure_ascii=False) + "\n")


def load_dataset(dataset: str) -> Dict[str, Dict[str, Any]]:
    path = REPO_ROOT / "data" / "dataset" / f"{dataset}.json"
    with path.open("r", encoding="utf-8") as f:
        data = json.load(f)
    return {str(row.get("name")): row for row in data if row.get("name")}


def infer_dataset(output_dir: Path) -> str:
    name = output_dir.name
    if name.startswith("matharena_"):
        return "matharena"
    if name.startswith("putnam_"):
        return "putnam"
    raise ValueError(f"Cannot infer dataset from output directory name: {output_dir}")


def strip_imports_and_options(code: str) -> str:
    lines = []
    for line in str(code or "").splitlines():
        stripped = line.strip()
        if stripped.startswith("import ") or stripped.startswith("set_option "):
            continue
        lines.append(line)
    return "\n".join(lines).strip()


def theorem_name_from_proof(proof: str, fallback: str) -> str:
    match = re.search(r"(?:^|\s)theorem\s+([A-Za-z_][A-Za-z0-9_'.]*)\b", proof or "")
    return match.group(1) if match else fallback


def fenced_blocks_from_infos(infos: Any) -> List[str]:
    blocks: List[str] = []
    for info in infos or []:
        if not isinstance(info, dict):
            continue
        data = str(info.get("data", ""))
        blocks.extend(block.strip() for block in re.findall(r"```(.*?)```", data, flags=re.DOTALL))
    return blocks


def parse_quoted_names(text: str) -> Set[str]:
    return set(re.findall(r"``([A-Za-z0-9_'.]+)", text or ""))


def format_invalid_constants(constants: Sequence[str]) -> List[str]:
    return [f"``{name}" for name in constants]


def normalize_bool(value: Any, default: bool = True) -> bool:
    if value is None:
        return default
    if isinstance(value, bool):
        return value
    text = str(value).strip().lower()
    if text in {"true", "1", "yes", "y"}:
        return True
    if text in {"false", "0", "no", "n"}:
        return False
    return default


def build_extract_tasks(
    rows: Sequence[Dict[str, Any]],
    dataset_by_name: Dict[str, Dict[str, Any]],
) -> List[Dict[str, str]]:
    tasks: List[Dict[str, str]] = []
    for row in rows:
        name = str(row.get("name") or "")
        entry = dataset_by_name.get(name, {})
        info = entry.get("formal_answer_info") or {}
        admissible = str(info.get("admissible_vocabulary") or "[]")
        allow_quantifier = normalize_bool(info.get("allow_quantifier"), True)
        proof = str(row.get("proof") or "")
        theorem_name = theorem_name_from_proof(proof, name)
        command = (
            strip_imports_and_options(proof)
            + f"\n\n#extract_first_exists_witness_reason {theorem_name} "
            + f"with admissible_vocabulary := {admissible} "
            + f"allow_quantifier := {'true' if allow_quantifier else 'false'}\n"
        )
        tasks.append({"name": str(row.get("generation_id") or name), "code": command})
    return tasks


def result_by_name(results: Sequence[Dict[str, Any]]) -> Dict[str, Dict[str, Any]]:
    return {str(row.get("name")): row for row in results}


def first_non_status_block(blocks: Sequence[str]) -> str:
    for block in blocks:
        stripped = block.strip()
        if stripped not in {"canonical", "not canonical"} and not stripped.startswith("[``"):
            return stripped
    return ""


def canonical_status_and_constants(result: Optional[Dict[str, Any]]) -> tuple[str, Set[str]]:
    if not result:
        return "not_run", set()
    comp = result.get("compilation_result") or {}
    blocks = fenced_blocks_from_infos(comp.get("infos"))
    status = "not_run"
    constants: Set[str] = set()
    for block in blocks:
        stripped = block.strip()
        if stripped in {"canonical", "not canonical"}:
            status = stripped
        elif stripped.startswith("["):
            constants |= parse_quoted_names(stripped)
    return status, constants


def witness_status_constants(result: Optional[Dict[str, Any]]) -> tuple[str, str, Set[str]]:
    if not result:
        return "", "not_run", set()
    comp = result.get("compilation_result") or {}
    blocks = fenced_blocks_from_infos(comp.get("infos"))
    witness = ""
    status = "not_run"
    constants: Set[str] = set()
    for block in blocks:
        stripped = block.strip()
        if stripped in {"canonical", "not canonical"}:
            status = stripped
        elif stripped.startswith("["):
            constants |= parse_quoted_names(stripped)
        elif not witness:
            witness = stripped
    return witness, status, constants


def quantifier_like(witness: str) -> bool:
    return any(token in witness for token in ("∃", "∀", "Exists", "forall"))


def _scan_until_top_level_comma(text: str, start: int) -> str:
    pairs = {"(": ")", "[": "]", "{": "}", "⟨": "⟩"}
    closing = {v: k for k, v in pairs.items()}
    stack: List[str] = []
    out: List[str] = []
    i = start
    while i < len(text):
        ch = text[i]
        if ch == "," and not stack:
            break
        out.append(ch)
        if ch in pairs:
            stack.append(ch)
        elif ch in closing and stack and stack[-1] == closing[ch]:
            stack.pop()
        i += 1
    return "".join(out).strip()


def syntactic_witness_fallback(proof: str) -> str:
    text = proof or ""
    match = re.search(r"\brefine'?\s*⟨", text)
    if match:
        return _scan_until_top_level_comma(text, match.end())
    match = re.search(r"^\s*use\s+(.+)$", text, flags=re.MULTILINE)
    if match:
        return match.group(1).strip()
    return ""


def heuristic_used_constants(text: str) -> Set[str]:
    constants = set(re.findall(r"\b[A-Z][A-Za-z0-9_']*(?:\.[A-Za-z0-9_']+)+", text or ""))
    if "∑" in text or ".sum" in text:
        constants.add("Finset.sum")
    if "∃" in text:
        constants.add("Exists")
    if "∧" in text:
        constants.add("And")
    if "=" in text:
        constants.add("Eq")
    if "+" in text:
        constants.add("HAdd.hAdd")
    if "*" in text:
        constants.add("HMul.hMul")
    if "^" in text:
        constants.add("HPow.hPow")
    if "∣" in text:
        constants.add("Dvd.dvd")
    if "≤" in text:
        constants.add("LE.le")
    return constants


def extract_for_output_dir(output_dir: Path, workers: int) -> Path:
    dataset = infer_dataset(output_dir)
    dataset_by_name = load_dataset(dataset)
    inadmissible_path = output_dir / "inadmissible_proofs.jsonl"
    output_path = output_dir / "inadmissible_proofs_reason.jsonl"
    rows = read_jsonl(inadmissible_path)
    if not rows:
        write_jsonl(output_path, [])
        return output_path

    worker_count = max(1, min(workers, len(rows)))
    results = scheduler(
        build_extract_tasks(rows, dataset_by_name),
        num_workers=worker_count,
        imports=IMPORTS_WITH_REASON_COMMAND,
    )
    results_by_key = result_by_name(results)

    reason_rows: List[Dict[str, Any]] = []
    for row in rows:
        name = str(row.get("name") or "")
        key = str(row.get("generation_id") or name)
        entry = dataset_by_name.get(name, {})
        info = entry.get("formal_answer_info") or {}
        admissible = parse_quoted_names(str(info.get("admissible_vocabulary") or "[]"))
        allow_quantifier = normalize_bool(info.get("allow_quantifier"), True)
        witness, status, used_constants = witness_status_constants(results_by_key.get(key))
        if not witness:
            witness = syntactic_witness_fallback(str(row.get("proof") or ""))
            if witness:
                status = "syntactic_fallback"
                used_constants = heuristic_used_constants(witness)
        invalid_constants = sorted(used_constants - admissible)
        invalid: Any = format_invalid_constants(invalid_constants)
        if not invalid and status == "not canonical" and (not allow_quantifier or quantifier_like(witness)):
            invalid = "quantifier"
        if not invalid and status == "syntactic_fallback":
            invalid = "syntactic_fallback_unchecked"
        if not invalid and not witness:
            invalid = "witness_not_extractable"
        reason_rows.append(
            {
                "name": name,
                "generation_id": row.get("generation_id", ""),
                "constructed_answer": witness,
                "ground truth answer": entry.get("formal_answer", ""),
                "invalid_used_constant": invalid,
            }
        )

    write_jsonl(output_path, reason_rows)
    return output_path


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("output_dirs", nargs="+", type=Path)
    parser.add_argument("--workers", type=int, default=16)
    args = parser.parse_args()

    os.chdir(REPO_ROOT)
    for output_dir in args.output_dirs:
        path = extract_for_output_dir(output_dir.resolve(), args.workers)
        print(f"wrote {path}", flush=True)


if __name__ == "__main__":
    main()
