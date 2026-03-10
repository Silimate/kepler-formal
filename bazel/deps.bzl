"""Module extension that maps git submodules to Bazel repos with overlay BUILD files.

This allows BUILD files to live in the parent repo (bazel/*.BUILD.bazel)
rather than inside submodule directories, so submodules don't need to be
forked or modified. When a submodule later gains native Bazel support,
the corresponding overlay can be removed.
"""

load("@bazel_tools//tools/build_defs/repo:local.bzl", "new_local_repository")

def _submodules_impl(module_ctx):
    # Get the root of the workspace to construct absolute paths
    # Each submodule gets a new_local_repository pointing to its checkout
    # with a BUILD file overlay from bazel/*.BUILD.bazel

    new_local_repository(
        name = "kissat",
        path = "thirdparty/kissat",
        build_file = "@@//bazel:kissat.BUILD.bazel",
    )

    new_local_repository(
        name = "glucose",
        path = "thirdparty/glucose",
        build_file = "@@//bazel:glucose.BUILD.bazel",
    )

    new_local_repository(
        name = "naja",
        path = "thirdparty/naja",
        build_file = "@@//bazel:naja.BUILD.bazel",
    )

submodules = module_extension(
    implementation = _submodules_impl,
)
