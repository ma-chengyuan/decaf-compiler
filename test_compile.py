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

    def run(path):
        proc = subprocess.Popen(
            [
                str(exec_name),
                "-t",
                "assembly",
                str(path),
                "--output",
                "./test_program.S",
                "--opt",
                "all",
            ],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        return proc

    def run_gcc():
        gcc = subprocess.Popen(
            ["gcc", "-O0", "-no-pie", "./test_program.S", "-o", "./test_program"],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        return gcc

    for test_type in ["codegen", "dataflow"]:
        for test_suite in ["../public-tests", "../private-tests"]:
            for input_type in ["input", "error"]:
                input_file_dir = Path(f"{test_suite}/{test_type}/{input_type}")
                if not input_file_dir.exists():
                    continue
                for input_file in os.listdir(input_file_dir):
                    if not input_file.endswith(".dcf"):
                        continue

                    total_cases += 1
                    test_case = TestCase(str(input_file_dir / input_file))
                    proc = run(input_file_dir / input_file)
                    compiler_stdout, stderr = proc.communicate()
                    if proc.returncode != 0:
                        test_case.unexpected_error(stderr.decode("utf-8"))
                        continue
                    gcc = run_gcc()
                    _, stderr = gcc.communicate()
                    if gcc.returncode != 0:
                        test_case.unexpected_error(stderr.decode("utf-8"))
                        continue
                    program = subprocess.Popen(
                        ["./test_program"],
                        stdout=subprocess.PIPE,
                        stderr=subprocess.PIPE,
                    )
                    stdout, stderr = program.communicate()
                    if input_type == "error":
                        if program.returncode != 0:
                            passed_cases += 1
                            test_case.expected_error("")
                        else:
                            test_case.unexpected_pass("Program did not error")
                    else:
                        if program.returncode != 0:
                            test_case.unexpected_error(stdout.decode("utf-8"))
                            continue
                        output_file = Path(
                            f"{test_suite}/{test_type}/output/{input_file}.out"
                        )
                        with open(output_file) as f:
                            expected_output = f.read()
                        stdout = stdout.decode("utf-8")
                        if stdout.strip() == expected_output.strip():
                            passed_cases += 1
                            test_case.expected_pass(compiler_stdout.decode("utf-8"))
                        else:
                            differ = difflib.Differ()
                            result = "\n".join(
                                differ.compare(
                                    stdout.splitlines(), expected_output.splitlines()
                                )
                            )
                            test_case.unexpected_error(result)

    print(f"Passed {passed_cases}/{total_cases} tests")


if __name__ == "__main__":
    main()
