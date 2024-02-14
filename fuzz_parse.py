import os
import random
import subprocess
import sys
from pathlib import Path

suffix = ".exe" if os.name == "nt" else ""
sys.setrecursionlimit(10**6)


class SyntacticElement:
    def generate(self) -> str:
        raise NotImplementedError


CFG: dict[str, SyntacticElement]


class T(SyntacticElement):
    def __init__(self, token: str):
        self.token = token

    def generate(self) -> str:
        return self.token


class N(SyntacticElement):
    def __init__(self, name: str):
        self.name = name

    def generate(self) -> str:
        try:
            return CFG[self.name].generate()
        except RecursionError:
            print(f"Recursion error at {self.name}")
            raise


class Seq(SyntacticElement):
    def __init__(self, *elements: SyntacticElement, sep=" "):
        self.elements = elements
        self.sep = sep

    def generate(self) -> str:
        return self.sep.join(e.generate() for e in self.elements).strip()


class Alt(SyntacticElement):
    def __init__(self, *elements: SyntacticElement):
        self.elements = elements

    def generate(self) -> str:
        return random.choice(self.elements).generate()


class CommaSepOneOrMore(SyntacticElement):
    def __init__(self, element: SyntacticElement):
        self.element = element

    def generate(self) -> str:
        return ", ".join(self.element.generate() for _ in range(random.randint(1, 5)))


class Opt(SyntacticElement):
    def __init__(self, element: SyntacticElement):
        self.element = element

    def generate(self) -> str:
        return self.element.generate() if random.choice([True, False]) else ""


class ZeroOrMore(SyntacticElement):
    def __init__(self, element: SyntacticElement, sep=" "):
        self.element = element
        self.sep = sep

    def generate(self) -> str:
        return self.sep.join(
            self.element.generate() for _ in range(random.randint(0, 3))
        ).strip()


class ID(SyntacticElement):
    def generate(self) -> str:
        return random.choice(
            ["a", "b", "c", "d", "e", "f", "g", "foo", "bar", "baz", "main"]
        )


class IntLiteral(SyntacticElement):
    def generate(self) -> str:
        digits = random.randint(1, 20)
        value = random.randint(0, 10**digits - 1)
        if random.random() < 0.5:
            return str(value)
        return f"0x{value:X}"


CFG = {
    "program": Seq(
        ZeroOrMore(N("import_decl"), sep="\n"),
        ZeroOrMore(N("field_decl"), sep="\n"),
        ZeroOrMore(N("method_decl"), sep="\n"),
        sep="\n",
    ),
    "import_decl": Seq(T("import"), N("id"), T(";")),
    "field_decl": Seq(
        Opt(T("const")),
        N("type"),
        CommaSepOneOrMore(
            Seq(
                Alt(Seq(N("id"), T("["), N("int_literal"), T("]")), N("id")),
                Opt(Seq(T("="), N("initializer"))),
            )
        ),
        T(";"),
    ),
    "method_decl": Seq(
        Alt(N("type"), T("void")),
        N("id"),
        T("("),
        Opt(CommaSepOneOrMore(Seq(N("type"), N("id")))),
        T(")"),
        N("block"),
    ),
    "block": Seq(
        T("{"), ZeroOrMore(N("field_decl")), ZeroOrMore(N("statement")), T("}")
    ),
    "type": Alt(T("int"), T("bool")),
    "initializer": Alt(N("literal"), N("array_literal")),
    "statement": Alt(
        Seq(N("location"), N("assign_expr"), T(";")),
        Seq(N("method_call"), T(";")),
        Seq(
            T("if"),
            T("("),
            N("expr"),
            T(")"),
            N("block"),
            Opt(Seq(T("else"), N("block"))),
        ),
        Seq(
            T("for"),
            T("("),
            N("id"),
            T("="),
            N("expr"),
            T(";"),
            N("expr"),
            T(";"),
            N("for_update"),
            T(")"),
            N("block"),
        ),
        Seq(T("while"), T("("), N("expr"), T(")"), N("block")),
        Seq(T("return"), N("expr"), T(";")),
        Seq(T("break"), T(";")),
        Seq(T("continue"), T(";")),
    ),
    "for_update": Alt(Seq(N("location"), N("assign_expr")), N("method_call")),
    "assign_expr": Alt(Seq(N("assign_op"), N("expr")), N("increment")),
    "assign_op": Alt(T("="), T("+="), T("-="), T("*="), T("/="), T("%=")),
    "increment": Alt(T("++"), T("--")),
    "method_call": Alt(
        Seq(N("method_name"), T("("), CommaSepOneOrMore(N("import_arg")), T(")")),
        Seq(N("method_name"), T("("), CommaSepOneOrMore(N("expr")), T(")")),
    ),
    "method_name": N("id"),
    "location": Alt(Seq(N("id"), Opt(Seq(T("["), N("expr"), T("]")))), N("id")),
    "expr": Alt(
        N("location"),
        N("method_call"),
        N("literal"),
        Seq(T("len"), T("("), N("id"), T(")")),
        Seq(N("expr"), N("bin_op"), N("expr")),
        Seq(T("-"), N("expr")),
        Seq(T("!"), N("expr")),
        Seq(T("("), N("expr"), T(")")),
    ),
    "import_arg": Alt(N("expr"), N("string_literal")),
    "bin_op": Alt(N("arith_op"), N("rel_op"), N("eq_op"), N("cond_op")),
    "arith_op": Alt(T("+"), T("-"), T("*"), T("/"), T("%")),
    "rel_op": Alt(T("<"), T(">"), T("<="), T(">=")),
    "eq_op": Alt(T("=="), T("!=")),
    "cond_op": Alt(T("&&"), T("||")),
    "literal": Alt(
        Seq(Opt(T("-")), N("int_literal")),
        N("char_literal"),
        N("bool_literal"),
    ),
    "array_literal": Seq(T("{"), CommaSepOneOrMore(N("literal")), T("}")),
    "id": ID(),
    "int_literal": IntLiteral(),
    "bool_literal": Alt(T("true"), T("false")),
    "char_literal": T("'a'"),
    "string_literal": T('"a"'),
}


def fuzz_test():
    with open("fuzz_out.dcf", "w") as f:
        f.write(CFG["program"].generate())
    exec_name = Path("target/debug/decaf-rust" + suffix)
    proc = subprocess.Popen(
        [str(exec_name), "-t", "parse", "fuzz_out.dcf"],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    stdout, stderr = proc.communicate()
    if proc.returncode != 0:
        print("FAILED")
        print(stderr.decode("utf-8"))
        exit(1)


def main():
    os.system("cargo build")
    for i in range(1000000):
        fuzz_test()
        if i % 100 == 0:
            print(f"Test {i} passed")


if __name__ == "__main__":
    main()
