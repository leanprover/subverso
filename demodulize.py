#!/usr/bin/env python3
"""
De-modulize Lean files by removing module system syntax.

Transformations:
1. Delete the first standalone "module" line
2. Replace "public import", "meta import", "public meta import" with "import"
3. Delete the first standalone "public section" line
4. Skip lines preceded by "-- nomodule skip"
"""

import sys
import re
from pathlib import Path


def demodulize_file(filepath):
    """De-modulize a single Lean file in place."""
    with open(filepath, 'r', encoding='utf-8') as f:
        lines = f.readlines()

    output_lines = []
    module_deleted = False
    public_section_deleted = False
    skip_next = False
    in_import_section = False

    for i, line in enumerate(lines):
        # Check for skip directive
        if re.match(r'--\s*nomodule\s+skip\s*', line):
            skip_next = True
            output_lines.append('')
            continue

        if skip_next:
            skip_next = False
            output_lines.append('')
            continue

        # Delete first standalone "module"
        if not module_deleted and line.strip() == 'module':
            module_deleted = True
            in_import_section = True
            output_lines.append('')
            continue

        # Delete first standalone "public section" (ends import section)
        if not public_section_deleted and line.strip() == 'public section':
            public_section_deleted = True
            in_import_section = False
            output_lines.append('')
            continue

        # Replace import variants with plain "import" (only in import section)
        modified_line = line
        if in_import_section:
            modified_line = re.sub(r'^\s*((public|meta)\s+)+import', 'import', modified_line)
        else:
            modified_line = re.sub(r'^\s*@\[\s*expose\s*\]', '-- @[expose]', modified_line)
            modified_line = re.sub(r':=\s*private', ':=', modified_line)
            modified_line = re.sub(r'meta\s+def', 'def', modified_line)
            modified_line = re.sub(r'meta\s+partial\s+def', 'partial def', modified_line)
            modified_line = re.sub(r'private\s+meta', 'private', modified_line)
            modified_line = re.sub(r'meta\s+instance', 'instance', modified_line)
            modified_line = re.sub(r'meta\s+partial\s+instance', 'partial instance', modified_line)
            modified_line = re.sub(r'meta\s+structure', 'structure', modified_line)
        output_lines.append(modified_line)

    with open(filepath, 'w', encoding='utf-8') as f:
        f.writelines(output_lines)


def main():
    """Find and de-modulize all .lean files in the specified directory tree."""
    if len(sys.argv) != 2:
        print("Usage: demodulize.py <directory>", file=sys.stderr)
        sys.exit(1)

    directory = Path(sys.argv[1])
    if not directory.is_dir():
        print(f"Error: {directory} is not a directory", file=sys.stderr)
        sys.exit(1)

    lean_files = directory.rglob('*.lean')

    count = 0
    for filepath in lean_files:
        demodulize_file(filepath)
        count += 1

    print(f"De-modulized {count} Lean files in {directory}")


if __name__ == '__main__':
    main()
