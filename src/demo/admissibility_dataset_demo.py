from __future__ import annotations

import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict


PROJECT_ROOT = Path(__file__).resolve().parents[2]
if str(PROJECT_ROOT) not in sys.path:
    sys.path.insert(0, str(PROJECT_ROOT))

from src.ecp.utils import (  # noqa: E402
    STRUCTURAL_OPTION_DEFAULTS,
    STRUCTURAL_OPTION_KEYS,
    ecp_preamble,
    verify_answer_admissibility,
)


DATASETS = {
    "matharena": PROJECT_ROOT / "data/dataset/matharena.json",
    "putnam": PROJECT_ROOT / "data/dataset/putnam.json",
}


@dataclass(frozen=True)
class TestCase:
    dataset: str
    problem: str
    label: str
    candidate_answer: str
    expected_admissible: bool


TEST_CASES = (
    TestCase("matharena", "P2026AIMEI_1", "literal_277", "277", True),
    TestCase("matharena", "P2026AIMEI_1", "add_zero", "(277 : Nat) + 0", False),
    TestCase("matharena", "P2026AIMEI_2", "literal_62", "62", True),
    TestCase("matharena", "P2026AIMEI_2", "nat_succ", "Nat.succ 61", False),
    TestCase("matharena", "P2026AIMEII_1", "literal_178", "178", True),
    TestCase("matharena", "P2026AIMEII_1", "mul_one", "(178 : Nat) * 1", False),
    TestCase(
        "putnam",
        "putnam_1962_a5",
        "formula",
        "fun n : ℕ => n * (n + 1) * 2^(n - 2)",
        True,
    ),
    TestCase("putnam", "putnam_1962_a5", "factorial_function", "fun n : ℕ => Nat.factorial n", False),
    TestCase(
        "putnam",
        "putnam_1972_a3",
        "affine_functions",
        "{f | ∃ A B : ℝ, ∀ x ∈ Set.Icc 0 1, f x = A * x + B}",
        True,
    ),
    TestCase("putnam", "putnam_1972_a3", "set_univ", "Set.univ", False),
)


def load_rows_by_name() -> Dict[str, Dict[str, Dict[str, Any]]]:
    datasets: Dict[str, Dict[str, Dict[str, Any]]] = {}
    for dataset, path in DATASETS.items():
        rows = json.loads(path.read_text(encoding="utf-8"))
        datasets[dataset] = {
            row["name"]: row
            for row in rows
            if isinstance(row, dict) and row.get("name")
        }
    return datasets


def short_vocabulary(row: Dict[str, Any]) -> str:
    info = row.get("formal_answer_info") or {}
    used = str(info.get("used_constants_in_ground_truth") or "").strip()
    if used and used != "[]":
        return used
    return str(info.get("admissible_vocabulary", "[]"))


def bool_from_raw(value: Any, default: bool) -> bool:
    if isinstance(value, bool):
        return value
    if value is None:
        return default
    text = str(value).strip().lower()
    if text in {"true", "1", "yes", "y", "on"}:
        return True
    if text in {"false", "0", "no", "n", "off"}:
        return False
    return default


def checker_info(row: Dict[str, Any]) -> Dict[str, Any]:
    info = row.get("formal_answer_info") or {}
    out: Dict[str, Any] = {
        "header": ecp_preamble(row),
        "answer_type": row["answer_type"],
        "admissible_vocabulary": short_vocabulary(row),
    }
    for key in STRUCTURAL_OPTION_KEYS:
        out[key] = bool_from_raw(info.get(key), STRUCTURAL_OPTION_DEFAULTS[key])
    return out


def switches_summary(row: Dict[str, Any]) -> str:
    info = row.get("formal_answer_info") or {}
    parts = []
    for key in STRUCTURAL_OPTION_KEYS:
        value = bool_from_raw(info.get(key), STRUCTURAL_OPTION_DEFAULTS[key])
        parts.append(f"{key}={str(value).lower()}")
    return ", ".join(parts)


def vocabulary_size(vocabulary: str) -> int:
    return len(re.findall(r"``[^,\]\s]+", vocabulary))


def one_line(text: Any, limit: int = 100) -> str:
    value = " ".join(str(text).split())
    if len(value) <= limit:
        return value
    return value[: limit - 3] + "..."


def check_case(case: TestCase, row: Dict[str, Any]) -> Dict[str, Any]:
    actual_admissible = verify_answer_admissibility(case.candidate_answer, checker_info(row))

    return {
        "dataset": case.dataset,
        "problem": case.problem,
        "label": case.label,
        "answer_type": row["answer_type"],
        "candidate_answer": case.candidate_answer,
        "actual_admissible": bool(actual_admissible),
        "expected_admissible": case.expected_admissible,
        "passed": bool(actual_admissible) == case.expected_admissible,
    }


def main() -> int:
    rows_by_name = load_rows_by_name()
    results = []

    print("Admissibility checker dataset smoke tests")
    print("Vocabulary source: formal_answer_info.used_constants_in_ground_truth")
    print("Switch source: raw formal_answer_info structural switches")
    print()

    current_problem = None
    for case in TEST_CASES:
        row = rows_by_name[case.dataset][case.problem]
        vocab = short_vocabulary(row)
        result = check_case(case, row)
        results.append(result)

        problem_key = (case.dataset, case.problem)
        if problem_key != current_problem:
            current_problem = problem_key
            print(f"{case.dataset}:{case.problem}")
            print(f"  answer_type: {row['answer_type']}")
            print(f"  switches: {switches_summary(row)}")
            print(f"  selected_vocabulary_size: {vocabulary_size(vocab)}")

        status = "PASS" if result["passed"] else "FAIL"
        print(
            f"  {status:<4} {case.label:<18} "
            f"expected={str(case.expected_admissible):<5} "
            f"actual={str(result['actual_admissible']):<5} "
            f"answer={one_line(result['candidate_answer'])}"
        )

    passed = sum(1 for result in results if result["passed"])
    total = len(results)
    print()
    print(f"Summary: {passed}/{total} passed")
    if passed != total:
        print("Failed cases:")
        for result in results:
            if not result["passed"]:
                print(
                    f"  {result['dataset']}:{result['problem']} {result['label']} "
                    f"expected={result['expected_admissible']} "
                    f"actual={result['actual_admissible']}"
                )
    return 0 if passed == total else 1


if __name__ == "__main__":
    raise SystemExit(main())
