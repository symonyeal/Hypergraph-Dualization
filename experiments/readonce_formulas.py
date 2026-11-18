"""Read-once formula inputs for the Rust live-support engine."""
import argparse


def gate(op, children):
    return f"({op} {' '.join(map(str, children))})"


def alternating(depth, arity, op, base=0):
    if depth == 0:
        return str(base)
    width = arity ** (depth - 1)
    other = "&" if op == "|" else "|"
    return gate(op, (alternating(depth - 1, arity, other, base + i * width)
                     for i in range(arity)))


def gk(k, base=0):
    return alternating(2 * k - 1, 2, "|", base)


def tk(k, base=0):
    return alternating(2 * k, 2, "&", base)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("family", choices=("gk", "tk"))
    parser.add_argument("k", type=int)
    args = parser.parse_args()
    if not 1 <= args.k <= (5 if args.family == "gk" else 4):
        parser.error("use GK 1..5 or TK 1..4")
    print({"gk": gk, "tk": tk}[args.family](args.k))
