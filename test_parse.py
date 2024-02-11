import difflib
import os
import subprocess
from pathlib import Path

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
    legal_file_dir = Path("../public-tests/parser/legal")
    illegal_file_dir = Path("../public-tests/parser/illegal")
    os.system("cargo build")
    exec_name = Path("target/debug/decaf-rust" + suffix)

    total_cases = 0
    passed_cases = 0

    def run(path):
        print(str(path), end=": ")
        proc = subprocess.Popen(
            [str(exec_name), "-t", "parse", str(path)],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        return proc

    for input_file in os.listdir(legal_file_dir):
        total_cases += 1
        proc = run(legal_file_dir / input_file)
        stdout, stderr = proc.communicate()
        if proc.returncode == 0:
            print("EXPECTED PASS")
            passed_cases += 1
        else:
            print("FAILED")
            print(
                "\n".join(
                    "    " + s for s in stderr.decode("utf-8").strip().splitlines()
                )
            )
            print("=" * 100)
    for input_file in os.listdir(illegal_file_dir):
        total_cases += 1
        proc = run(illegal_file_dir / input_file)
        stdout, stderr = proc.communicate()
        if proc.returncode != 0:
            print("EXPECTED FAIL")
            print(
                "\n".join(
                    "    " + s for s in stderr.decode("utf-8").strip().splitlines()
                )
            )
            passed_cases += 1
        else:
            print("FAILED")
            print("=" * 100)
    print(f"Passed {passed_cases}/{total_cases} tests")


if __name__ == "__main__":
    main()
