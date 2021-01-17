#!/bin/bash

set -eu

cat <<'EOF'
name: Remote Bench

on: push

jobs:
  submit:
    runs-on: ubuntu-latest
    outputs:
      benchid: ${{ steps.submit.outputs.benchid }}
    steps:
      - id: submit
        name: Submit
        run: |
          echo "${{ secrets.BENCH_KEY }}" > bench-key
          chmod 600 bench-key
          BENCHID=$(ssh -i bench-key -o StrictHostKeyChecking=no -o LogLevel=error \
              ${{ secrets.BENCH_HOST }} http://github.com/${{ github.repository }}.git \
              $GITHUB_SHA coq-tactician-stdlib.8.11.dev \"Set Tactician Benchmark 40\")
          echo $BENCHID
          echo "::set-output name=benchid::$BENCHID"
EOF

NEEDS="[submit]"
IF=
ATTACH=$(cat <<'EOF'
          echo "${{ needs.submit.outputs.benchid }}"
          echo "${{ secrets.ATTACH_KEY }}" > attach-key
          chmod 600 attach-key
          set -o pipefail
          set +e
          timeout 355m ssh -tt -i attach-key -o StrictHostKeyChecking=no -o LogLevel=error \
                  ${{ secrets.BENCH_HOST }} ${{ needs.submit.outputs.benchid }}
          EXIT=$?
          echo "Exit code $EXIT"
          if [ $EXIT -eq 124 ]; then
              echo "::set-output name=finished::false"
              echo "Job did not finish before Github time limit, spilling to next step"
          else
              exit $EXIT
          fi
EOF
)

for i in {0..13}; do
    cat << EOF
  attach${i}:
    runs-on: ubuntu-latest
    needs: $NEEDS
    outputs:
      finished: \${{ steps.attach.outputs.finished }}
    $IF
    steps:
      - id: attach
        name: Attach
        run: |
$ATTACH
EOF
    NEEDS="[submit, attach${i}]"
    IF="if: \${{ needs.attach${i}.outputs.finished == 'false' }}"
done
