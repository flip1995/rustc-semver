import json
import argparse

PARSER = argparse.ArgumentParser()
PARSER.add_argument("file", help="The coverage file")


def main():
    args = PARSER.parse_args()
    with open(args.file, 'r') as f:
        cov = json.load(f)

    line_coverage = cov["data"][0]["totals"]["lines"]["percent"]

    if line_coverage == 100:
        exit(0)
    else:
        exit(1)


if __name__ == "__main__":
    main()
