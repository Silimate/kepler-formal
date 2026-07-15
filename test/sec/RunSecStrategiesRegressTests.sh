#!/usr/bin/env bash
# Copyright 2024-2026 keplertech.io
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

helper="$1"
tmp_dir="$(mktemp -d "${TMPDIR:-/tmp}/kepler-sec-regress-test.XXXXXX")"
trap 'rm -rf "${tmp_dir}"' EXIT

# Copy the helper so its output directory also stays inside the temporary tree.
mkdir -p "${tmp_dir}/repo/regress" "${tmp_dir}/case"
cp "${helper}" "${tmp_dir}/repo/regress/run_sec_strategies_regress.sh"
printf 'verification: sec\n' > "${tmp_dir}/case/config.yaml"

cat > "${tmp_dir}/fake-kepler-formal" <<'EOF'
#!/usr/bin/env bash
echo "SEC partially proved equivalence at k = 1: 1/2 outputs proved; remaining outputs are inconclusive."
exit 2
EOF
chmod +x "${tmp_dir}/fake-kepler-formal"

for expectation in allow-inconclusive allow-unset-state-inconclusive; do
  bash "${tmp_dir}/repo/regress/run_sec_strategies_regress.sh" \
    "partial-${expectation}" \
    "${tmp_dir}/case" \
    "${tmp_dir}/fake-kepler-formal" \
    config.yaml \
    "${expectation}" \
    engine=pdr
done
