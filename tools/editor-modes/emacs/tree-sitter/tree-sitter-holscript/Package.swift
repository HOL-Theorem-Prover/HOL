// swift-tools-version:5.3
import PackageDescription

let package = Package(
    name: "TreeSitterHolscript",
    products: [
        .library(name: "TreeSitterHolscript", targets: ["TreeSitterHolscript"]),
    ],
    dependencies: [
        .package(url: "https://github.com/ChimeHQ/SwiftTreeSitter", from: "0.8.0"),
    ],
    targets: [
        .target(
            name: "TreeSitterHolscript",
            dependencies: [],
            path: ".",
            sources: [
                "src/parser.c",
                // NOTE: if your language has an external scanner, add it here.
            ],
            resources: [
                .copy("queries")
            ],
            publicHeadersPath: "bindings/swift",
            cSettings: [.headerSearchPath("src")]
        ),
        .testTarget(
            name: "TreeSitterHolscriptTests",
            dependencies: [
                "SwiftTreeSitter",
                "TreeSitterHolscript",
            ],
            path: "bindings/swift/TreeSitterHolscriptTests"
        )
    ],
    cLanguageStandard: .c11
)
