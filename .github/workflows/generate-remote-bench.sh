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
              ${{ secrets.BENCH_HOST }} http://github.com/${{ github.repository }}.git $GITHUB_SHA BENCHMARK=40)
          echo $BENCHID
          echo "::set-output name=benchid::$BENCHID"
          sleep 1m
EOF

NEEDS="[submit]"
IF=
ATTACH=$(cat <<'EOF'
          echo "${{ needs.submit.outputs.benchid }}"
          echo "${{ secrets.ATTACH_KEY }}" > attach-key
          chmod 600 attach-key
          set -o pipefail
          set +e
          ssh -i attach-key -o StrictHostKeyChecking=no -o LogLevel=error \
              ${{ secrets.BENCH_HOST }} ${{ needs.submit.outputs.benchid }}. 2>&1 | tee output.txt
          if [ $? -ne 0 ]; then
              if grep -q "Job is pending execution" output.txt; then
                  echo "::set-output name=finished::false"
                  echo "Sleeping 2h to wait for job execution"
                  sleep 2h
              else
                  exit 1
              fi
          fi
EOF
)

for i in {0..36}; do
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
