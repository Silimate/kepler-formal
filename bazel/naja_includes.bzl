"""Include flags for compiling Kepler targets against Bazel-fetched Naja.

Bazel's transitive `includes` are emitted as system include paths.  On macOS a
host-installed Naja under /usr/local/include can otherwise win the short
`#include "DNL.h"` lookup before the fetched @naja headers are considered.
"""

NAJA_HEADER_COPTS = [
    # Kepler and Naja's headers require C++20. The root module sets this via
    # .bazelrc (--cxxopt=-std=c++20), but that does not reach a downstream
    # consumer, so set it on the targets themselves.
    "-std=c++20",
    "-iquoteexternal/+deps+naja/src/src/dnl",
    "-iquoteexternal/+deps+naja/src/src/nl/netlist/core",
    "-iquoteexternal/+deps+naja/src/src/nl/netlist/snl",
    "-iquoteexternal/+deps+naja/src/src/core",
    "-iquoteexternal/+deps+naja/src/src/bne",
    "-iquoteexternal/+deps+naja/src/src/metrics",
    "-iquoteexternal/+deps+naja/src/src/nl/netlist/decorators",
    "-iquoteexternal/+deps+naja/src/src/nl/netlist/pnl",
    "-iquoteexternal/+deps+naja/src/src/nl/netlist/visual",
    "-iquoteexternal/+deps+naja/src/src/nl/netlist/serialization/capnp",
    "-iquoteexternal/+deps+naja/src/src/nl/formats/lefdef",
    "-iquoteexternal/+deps+naja/src/src/nl/formats/liberty",
    "-iquoteexternal/+deps+naja/src/src/nl/formats/systemverilog/frontend",
    "-iquoteexternal/+deps+naja/src/src/nl/formats/verilog/backend",
    "-iquoteexternal/+deps+naja/src/src/nl/formats/verilog/frontend",
    "-iquoteexternal/+deps+naja/src/src/nl/python/pyloader",
    "-iquoteexternal/+deps+naja/src/src/optimization",
    "-iquoteexternal/+deps+naja/src/thirdparty/cpptrace/include",
    "-iquoteexternal/+deps+naja/src/thirdparty/naja-verilog/src",
    "-iquoteexternal/+deps+naja/src/thirdparty/yosys-liberty/src",
    "-iquoteexternal/+deps+naja/src/thirdparty/lefdef/src/def/def",
]
