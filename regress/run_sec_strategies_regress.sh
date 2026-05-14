#!/usr/bin/env bash
# Copyright 2024-2026 keplertech.io
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

if [[ $# -lt 4 ]]; then
  echo "Usage: $0 <test-name> <case-dir> <kepler-formal-bin> <config-path> [expect-equivalent|expect-different] [max-k=<n>] [compact]" >&2
  exit 2
fi

test_name="$1"
case_dir="$2"
kepler_formal_bin="$3"
config_path="$4"
expectation=""
max_k_override=""
compact_mode=""

for option in "${@:5}"; do
  case "${option}" in
    expect-equivalent|expect-different)
      expectation="${option}"
      ;;
    compact)
      compact_mode="1"
      ;;
    max-k=*)
      max_k_override="${option#max-k=}"
      if [[ ! "${max_k_override}" =~ ^[0-9]+$ ]]; then
        echo "Invalid max-k override: ${max_k_override}" >&2
        exit 2
      fi
      ;;
    *)
      echo "Unknown option: ${option}" >&2
      exit 2
      ;;
  esac
done

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "${script_dir}/.." && pwd)"
output_dir="${repo_root}/regress-output/${test_name}/sec"

mkdir -p "${output_dir}"

run_engine() {
  local engine="$1"
  local tmp_config="${output_dir}/config.${engine}.yaml"
  local output_log="${output_dir}/${engine}.log"
  local stdout_log="${output_dir}/${engine}.stdout"

  (
    cd "${case_dir}"
    # SEC currently rejects CNF-export options, and every engine needs its own
    # log/config pair. Keep the design, library, solver, and max_k settings from
    # the original regression config, then override only the verification mode
    # and the selected top-level SEC strategy.
    awk -v max_k_override="${max_k_override}" -v compact_mode="${compact_mode}" '
      /^[[:space:]]*verification:/ { next }
      /^[[:space:]]*sec_engine:/ { next }
      /^[[:space:]]*max_k:/ {
        if (max_k_override != "") {
          next
        }
      }
      /^[[:space:]]*compact_mode:/ {
        if (compact_mode != "") {
          next
        }
      }
      /^[[:space:]]*cnf_export:/ { next }
      /^[[:space:]]*cnf_export_path:/ { next }
      /^[[:space:]]*po_cnf_export:/ { next }
      /^[[:space:]]*po_cnf_export_path:/ { next }
      /^[[:space:]]*log_file:/ { next }
      { print }
    ' "${config_path}" > "${tmp_config}"
    {
      echo
      echo "log_file: ${output_log}"
      echo "verification: sec"
      echo "sec_engine: ${engine}"
      if [[ -n "${max_k_override}" ]]; then
        echo "max_k: ${max_k_override}"
      fi
      if [[ -n "${compact_mode}" ]]; then
        echo "compact_mode: true"
      fi
    } >> "${tmp_config}"

    echo "Running SEC ${engine} for ${test_name}"
    "${kepler_formal_bin}" --config "${tmp_config}" > "${stdout_log}" 2>&1
    cat "${stdout_log}"

    if [[ "${expectation}" == "expect-equivalent" ]]; then
      grep "SEC proved equivalence" "${output_log}"
    elif [[ "${expectation}" == "expect-different" ]]; then
      grep "SEC found a counterexample" "${output_log}"
    else
      grep -E "SEC proved equivalence|SEC found a counterexample" "${output_log}"
    fi
  )
}

for engine in k_induction imc pdr; do
  run_engine "${engine}"
done
