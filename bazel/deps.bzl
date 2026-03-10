"""Module extension that fetches third-party dependencies via http_archive.

For BCR compatibility, dependencies are fetched as source archives from
GitHub rather than relying on git submodules. The cmake flow continues
to use submodules directly (thirdparty/).

When a dependency gains native Bazel support or is published to BCR,
replace the corresponding http_archive with a bazel_dep in MODULE.bazel.
"""

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def _naja_repo_impl(repo_ctx):
    """Repository rule that assembles naja from multiple archives.

    Naja has a nested submodule (naja-verilog) that must be placed at
    thirdparty/naja-verilog/. The whole tree is then placed under src/
    to match the overlay BUILD file paths used by cmake_submodule_repo.

    Any BUILD/BUILD.bazel files in the archives are excluded so the
    entire tree is a single Bazel package (required by rules_foreign_cc
    cmake()).
    """
    # Download naja main archive
    repo_ctx.download_and_extract(
        url = repo_ctx.attr.naja_url,
        sha256 = repo_ctx.attr.naja_sha256,
        stripPrefix = repo_ctx.attr.naja_strip_prefix,
        output = "src",
    )

    # Download naja-verilog archive into the expected subdirectory
    repo_ctx.download_and_extract(
        url = repo_ctx.attr.naja_verilog_url,
        sha256 = repo_ctx.attr.naja_verilog_sha256,
        stripPrefix = repo_ctx.attr.naja_verilog_strip_prefix,
        output = "src/thirdparty/naja-verilog",
    )

    # Remove any BUILD files from archives to avoid package boundary issues
    repo_ctx.execute(["find", "src", "-name", "BUILD", "-o", "-name", "BUILD.bazel"], quiet = True)
    result = repo_ctx.execute(["find", "src", "(", "-name", "BUILD", "-o", "-name", "BUILD.bazel", ")", "-delete"])
    if result.return_code != 0:
        fail("Failed to clean BUILD files: " + result.stderr)

    # Write the overlay BUILD file
    repo_ctx.file("BUILD.bazel", repo_ctx.read(repo_ctx.attr.build_file))

naja_repo = repository_rule(
    implementation = _naja_repo_impl,
    attrs = {
        "naja_url": attr.string(mandatory = True),
        "naja_sha256": attr.string(mandatory = True),
        "naja_strip_prefix": attr.string(mandatory = True),
        "naja_verilog_url": attr.string(mandatory = True),
        "naja_verilog_sha256": attr.string(mandatory = True),
        "naja_verilog_strip_prefix": attr.string(mandatory = True),
        "build_file": attr.label(mandatory = True),
    },
)

# Pinned dependency versions (commit SHAs from thirdparty/ submodules).
# To update: change the commit, run `bazel fetch @glucose @kissat @naja`
# to verify, then update the sha256 hashes.
_GLUCOSE_COMMIT = "7f887abba7cf13636a5ac2d28653668a20a91b25"
_KISSAT_COMMIT = "8af8e56f174b778aef3aa45af9f739b2a5f492c2"
_NAJA_COMMIT = "7bf03dee61889f46717313683904ac7737f7c886"
_NAJA_VERILOG_COMMIT = "a377d7f2644bbbf98ff1ae9e8511d52eba8dd6ca"

def _deps_impl(_module_ctx):
    http_archive(
        name = "glucose",
        url = "https://github.com/audemard/glucose/archive/{}.tar.gz".format(_GLUCOSE_COMMIT),
        sha256 = "3033a27047f35653f63559e4f31d664cb8b57a7dcdab9d90233be1d1f52f4eda",
        strip_prefix = "glucose-{}".format(_GLUCOSE_COMMIT),
        build_file = "@@//bazel:glucose.BUILD.bazel",
    )

    http_archive(
        name = "kissat",
        url = "https://github.com/arminbiere/kissat/archive/{}.tar.gz".format(_KISSAT_COMMIT),
        sha256 = "9268b6daaf76ea34ea9da503338beddc5539eb783d1a83a37a7af2a028f3b236",
        strip_prefix = "kissat-{}".format(_KISSAT_COMMIT),
        build_file = "@@//bazel:kissat.BUILD.bazel",
    )

    naja_repo(
        name = "naja",
        naja_url = "https://github.com/nanocoh/naja/archive/{}.tar.gz".format(_NAJA_COMMIT),
        naja_sha256 = "95ee90477fa46a7de23e1ddb274dd1677d0c0e6c7dd260f2e7776ba62462eb60",
        naja_strip_prefix = "naja-{}".format(_NAJA_COMMIT),
        naja_verilog_url = "https://github.com/najaeda/naja-verilog/archive/{}.tar.gz".format(_NAJA_VERILOG_COMMIT),
        naja_verilog_sha256 = "beffd84e14da4b146d9a0dc4699ebf44596cd437cf8157e3b39430a4080c606d",
        naja_verilog_strip_prefix = "naja-verilog-{}".format(_NAJA_VERILOG_COMMIT),
        build_file = "@@//bazel:naja.BUILD.bazel",
    )

deps = module_extension(
    implementation = _deps_impl,
)
