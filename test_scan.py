import difflib
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

    for test_suite in ["public", "private"]:
        input_file_dir = Path(f"../{test_suite}-tests/scanner/input")
        output_file_dir = Path(f"../{test_suite}-tests/scanner/output")
        for input_file in os.listdir(input_file_dir):
            total_cases += 1
            base, _ = os.path.splitext(input_file)
            output_file = output_file_dir / (base + ".out")
            test_case = TestCase(str(input_file_dir / input_file))
            proc = subprocess.Popen(
                [str(exec_name), "-t", "scan", str(input_file_dir / input_file)],
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
            )
            stdout, stderr = proc.communicate()
            output = stdout.decode("utf-8")
            with open(output_file, "r") as f:
                ref_output = f.read()
            output_valid = proc.returncode == 0
            ref_output_valid = is_valid(ref_output)
            if output_valid != ref_output_valid:
                print(f"Test {input_file} failed: output is not valid")
                print(f"Output: {output}")
                print(f"Ref output: {ref_output}")
                continue
            if output_valid:
                output = output.strip()
                ref_output = ref_output.strip()
                if output != ref_output:
                    differ = difflib.Differ()
                    result = "\n".join(
                        differ.compare(output.splitlines(), ref_output.splitlines())
                    )
                    print(f"Test {input_file} failed: output is not correct")
                    print(result)
                    continue
                test_case.expected_pass()
            else:
                test_case.expected_error(stderr.decode("utf-8"))
            passed_cases += 1

    print(f"Passed {passed_cases}/{total_cases} tests")


if __name__ == "__main__":
    main()
