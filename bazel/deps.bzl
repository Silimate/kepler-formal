"""Module extension that maps git submodules to Bazel repos with overlay BUILD files.

This allows BUILD files to live in the parent repo (bazel/*.BUILD.bazel)
rather than inside submodule directories, so submodules don't need to be
forked or modified. When a submodule later gains native Bazel support,
the corresponding overlay can be removed.
"""

load("@bazel_tools//tools/build_defs/repo:local.bzl", "new_local_repository")

def _cmake_submodule_repo_impl(repo_ctx):
    """Repository rule that copies a source tree excluding BUILD files.

    This is needed for rules_foreign_cc cmake() because glob(["**"])
    doesn't cross Bazel package boundaries. Submodules like googletest
    have their own BUILD.bazel files that create unwanted sub-packages.
    Copying without them makes the entire tree visible as a single package.
    """
    ws_root = repo_ctx.path(repo_ctx.attr.anchor).dirname
    src_path = str(ws_root) + "/" + repo_ctx.attr.path

    # Copy the entire tree, excluding BUILD and BUILD.bazel files
    repo_ctx.execute(
        ["rsync", "-a", "--exclude=BUILD", "--exclude=BUILD.bazel", src_path + "/", "src/"],
    )

    # Write the overlay BUILD file
    build_content = repo_ctx.read(repo_ctx.attr.build_file)
    repo_ctx.file("BUILD.bazel", build_content)

cmake_submodule_repo = repository_rule(
    implementation = _cmake_submodule_repo_impl,
    attrs = {
        "path": attr.string(mandatory = True, doc = "Workspace-relative path to submodule"),
        "build_file": attr.label(mandatory = True, doc = "BUILD file overlay"),
        "anchor": attr.label(mandatory = True, doc = "Label in workspace root to resolve paths from"),
    },
    local = True,
)

def _submodules_impl(_module_ctx):
    # Simple submodules: new_local_repository with BUILD file overlay
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

    # Naja needs special handling: nested submodules contain BUILD files
    # that create package boundaries blocking glob(["**"]).
    # cmake_submodule_repo copies the tree excluding BUILD files so the
    # cmake() rule can see the entire source tree as one package.
    cmake_submodule_repo(
        name = "naja",
        path = "thirdparty/naja",
        build_file = "@@//bazel:naja.BUILD.bazel",
        anchor = "@@//:BUILD.bazel",
    )

submodules = module_extension(
    implementation = _submodules_impl,
)
