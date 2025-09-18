import argparse
import sys
import urllib.request
from pathlib import Path
from license_expression import get_spdx_licensing

def eprint(*args, **kwargs):
    print(*args, file=sys.stderr, **kwargs)

def main():
    parser = argparse.ArgumentParser(
        description = 'A tactic prediction server acting as an oracle, retrieving it\'s information from a dataset',
        formatter_class=argparse.ArgumentDefaultsHelpFormatter)

    parser.add_argument('dataset',
                        type=str,
                        help=('The root of the dataset.'))
    parser.add_argument('package',
                        type=str,
                        help=('The name of the package.'))
    parser.add_argument('summary',
                        type=str,
                        help=('The summary of the package.'))
    parser.add_argument('homepage',
                        type=str,
                        help=('The homepage of the package.'))
    parser.add_argument('authors',
                        type=str,
                        help=('The authors of the package.'))
    parser.add_argument('license',
                        type=str,
                        help=('The license of the package.'))
    args = parser.parse_args()
    dataset = Path(args.dataset)

    licensing = get_spdx_licensing()
    try:
        validated = licensing.validate(args.license)
    except AttributeError: # Work around bug in license_expression
        validated = licensing.validate('Error')
    if validated.normalized_expression is None or validated.normalized_expression == 'None':
        eprint("\n===========================================\n"
               f"Licensing errors for package {args.package}:\n{args.license}"
               )
        for err in validated.errors:
            eprint(f"    {err}")
        eprint("===========================================\n")
        license = args.license
        extra_text = "No license files could be retrieved"
    else:
        license = validated.normalized_expression
        license_files = [ lic + '.txt' for lic in
                          licensing.license_keys(validated.normalized_expression, unique=True)]
        extra_text = "License texts can be found in: " + ' '.join(license_files)

        for lic in license_files:
            url = 'https://raw.githubusercontent.com/spdx/license-list-data/main/text/' + lic
            fname = dataset / 'dataset' / args.package / lic
            with urllib.request.urlopen(url) as response, open(fname, 'wb') as out_file:
                data = response.read()
                out_file.write(data)

    summary_base = (
f"""- Package   : {args.package}
  + Summary : {args.summary}
  + Homepage: <{args.homepage}>
  + Authors : {args.authors}
  + License : {license}""")

    summary_expanded = summary_base + '\n\n' + extra_text

    with open(dataset / 'README.md', 'a') as readme:
        readme.write('\n' + summary_base)

    with open(dataset / 'dataset' / args.package / 'LICENSE', 'w') as license:
        license.write('\n' + summary_expanded)

if __name__ == '__main__':
    main()
