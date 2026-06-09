TBB_DEPS = select({
    "@platforms//os:macos": ["@homebrew_tbb//:tbb"],
    "//conditions:default": [],
})

TBB_LINKOPTS = select({
    "@platforms//os:macos": [
        "-L/opt/homebrew/lib",
        "-L/usr/local/lib",
        "-ltbb",
        "-ltbbmalloc",
    ],
    "//conditions:default": [
        "-ltbb",
        "-ltbbmalloc",
    ],
})
