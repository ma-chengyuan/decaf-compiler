import os
import shutil
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
            [
                "gcc",
                "-O0",
                "-no-pie",
                "./test_program.S",
                "-L../public-tests/derby/lib",
                "-l6035_linux_x86",
                "-o",
                "./test_program",
            ],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        return gcc

    for test_suite in ["../public-tests"]:
        input_file_dir = Path(f"{test_suite}/derby/input")
        if not input_file_dir.exists():
            continue
        output_file_dir = Path(f"{test_suite}/derby/output")
        if not output_file_dir.exists():
            output_file_dir.mkdir(parents=True)
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
                ["../../compiler/test_program"],
                cwd="../public-tests/derby/",
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
            )
            stdout, stderr = program.communicate()

            if program.returncode != 0:
                test_case.unexpected_error(stderr.decode("utf-8"))
                continue
            input_file = input_file.removesuffix(".dcf")
            expected_file = Path(f"{test_suite}/derby/expected/{input_file}.pgm")
            with open(expected_file, "br") as f:
                expected_output = f.read()
            output_file = Path(f"{test_suite}/derby/output/{input_file}.pgm")
            with open(output_file, "br") as f:
                output = f.read()
            if output != expected_output:
                test_case.unexpected_error("Output does not match expected output")
            else:
                passed_cases += 1
                test_case.expected_pass(stdout.decode("utf-8"))
                print(compiler_stdout.decode("utf-8"))

    print(f"Passed {passed_cases}/{total_cases} tests")

    # return
    if passed_cases == total_cases and shutil.which("hyperfine"):
        for test_suite in ["../public-tests"]:
            input_file_dir = Path(f"{test_suite}/derby/input")
            if not input_file_dir.exists():
                continue
            output_file_dir = Path(f"{test_suite}/derby/output")
            if not output_file_dir.exists():
                output_file_dir.mkdir(parents=True)
            for input_file in os.listdir(input_file_dir):
                if not input_file.endswith(".dcf"):
                    continue
                proc = run(input_file_dir / input_file)
                _, stderr = proc.communicate()
                assert proc.returncode == 0
                gcc = run_gcc()
                _, stderr = gcc.communicate()
                assert gcc.returncode == 0
                print(f"Running hyperfine on {input_file}")
                benchmark = subprocess.Popen(
                    ["hyperfine", "--warmup", "5", "../../compiler/test_program"],
                    cwd="../public-tests/derby/",
                )
                benchmark.communicate()


if __name__ == "__main__":
    main()
