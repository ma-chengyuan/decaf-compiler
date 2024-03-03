import os
import subprocess
from pathlib import Path

from test_util import TestCase

suffix = ".exe" if os.name == "nt" else ""


def is_valid(output: str):
    for line in output.split("\n"):
        line = line.strip()
        if not line:
            continue
        try:
            int(line.split(" ")[0])
        except ValueError:
            return False
    return True


def main():
    total_cases = 0
    passed_cases = 0

    os.system("cargo build")
    exec_name = Path("target/debug/decaf-rust" + suffix)

    def run(path):
        proc = subprocess.Popen(
            [str(exec_name), "-t", "inter", str(path)],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        return proc

    for test_suite in ["../public-tests", "./tests"]:
        legal_file_dir = Path(f"{test_suite}/semantics/legal")
        illegal_file_dir = Path(f"{test_suite}/semantics/illegal")

        for input_file in os.listdir(legal_file_dir):
            total_cases += 1
            test_case = TestCase(str(legal_file_dir / input_file))
            proc = run(legal_file_dir / input_file)
            _, stderr = proc.communicate()
            if proc.returncode == 0:
                test_case.expected_pass(stderr.decode("utf-8"))
                passed_cases += 1
            else:
                test_case.unexpected_error(stderr.decode("utf-8"))
        for input_file in os.listdir(illegal_file_dir):
            total_cases += 1
            test_case = TestCase(str(illegal_file_dir / input_file))
            proc = run(illegal_file_dir / input_file)
            _, stderr = proc.communicate()
            if proc.returncode != 0:
                test_case.expected_error(stderr.decode("utf-8"))
                passed_cases += 1
            else:
                test_case.unexpected_pass()
    print(f"Passed {passed_cases}/{total_cases} tests")


if __name__ == "__main__":
    main()
