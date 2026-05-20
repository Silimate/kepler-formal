#!/usr/bin/env bash
# Copyright 2024-2026 keplertech.io
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

if [[ $# -lt 4 ]]; then
  echo "Usage: $0 <test-name> <case-dir> <kepler-formal-bin> <config-path> [expect-equivalent|expect-different] [max-k=<n>] [compact] [engine=<name>]" >&2
  exit 2
fi

test_name="$1"
case_dir="$2"
kepler_formal_bin="$3"
config_path="$4"
expectation=""
max_k_override=""
compact_mode=""
# By default the helper is useful for local all-engine smoke checks.  CI passes
# engine=<name> from the split regress workflows so each job owns one strategy.
engines=(k_induction imc pdr)

for option in "${@:5}"; do
  case "${option}" in
    expect-equivalent|expect-different)
      expectation="${option}"
      ;;
    compact)
      compact_mode="1"
      ;;
    engine=*)
      engine="${option#engine=}"
      case "${engine}" in
        k_induction|imc|pdr)
          engines=("${engine}")
          ;;
        *)
          echo "Invalid SEC engine override: ${engine}" >&2
          exit 2
          ;;
      esac
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
  local stdout_log="${output_dir}/${engine}.stdout"

  (
    cd "${case_dir}"
    # SEC currently rejects CNF-export options. Keep the design, library, and
    # solver settings from the original regression config, then override only
    # the verification mode and selected SEC strategy. Drop LEC max_k by
    # default: PDR proves by frame convergence and the split SEC regressions
    # should not accidentally inherit toy bounded-check depths such as k=4.
    # Do not force a log_file here: repeated local regress runs are easier to
    # inspect when kepler-formal keeps its own per-run log naming.
    awk -v max_k_override="${max_k_override}" -v compact_mode="${compact_mode}" '
      /^[[:space:]]*verification:/ { next }
      /^[[:space:]]*sec_engine:/ { next }
      /^[[:space:]]*max_k:/ { next }
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
    : > "${stdout_log}"
    # Stream the tool output as it is produced instead of only dumping it after
    # completion.  Large SEC/PDR cases can run for minutes between solver
    # decisions, so emit a lightweight heartbeat to keep GitHub logs obviously
    # alive and to make a true hang easier to distinguish from solver work.
    "${kepler_formal_bin}" --config "${tmp_config}" > "${stdout_log}" 2>&1 &
    local kepler_pid=$!
    tail -n +1 -f "${stdout_log}" &
    local tail_pid=$!
    local kepler_status=0
    local heartbeat_elapsed=0
    while kill -0 "${kepler_pid}" 2>/dev/null; do
      sleep 5
      heartbeat_elapsed=$((heartbeat_elapsed + 5))
      if [[ "${heartbeat_elapsed}" -ge 60 ]] &&
          kill -0 "${kepler_pid}" 2>/dev/null; then
        printf '[%s] SEC %s for %s is still running...\n' \
          "$(date -u '+%Y-%m-%dT%H:%M:%SZ')" "${engine}" "${test_name}"
        heartbeat_elapsed=0
      fi
    done
    wait "${kepler_pid}" || kepler_status=$?
    sleep 1
    kill "${tail_pid}" 2>/dev/null || true
    wait "${tail_pid}" 2>/dev/null || true
    if [[ "${kepler_status}" -ne 0 ]]; then
      return "${kepler_status}"
    fi

    if [[ "${expectation}" == "expect-equivalent" ]]; then
      grep "SEC proved equivalence" "${stdout_log}"
    elif [[ "${expectation}" == "expect-different" ]]; then
      grep "SEC found a counterexample" "${stdout_log}"
    else
      grep -E "SEC proved equivalence|SEC found a counterexample" "${stdout_log}"
    fi
  )
}

for engine in "${engines[@]}"; do
  run_engine "${engine}"
done
