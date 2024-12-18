import XCTest
import SwiftTreeSitter
import TreeSitterHolscript

final class TreeSitterHolscriptTests: XCTestCase {
    func testCanLoadGrammar() throws {
        let parser = Parser()
        let language = Language(language: tree_sitter_holscript())
        XCTAssertNoThrow(try parser.setLanguage(language),
                         "Error loading Holscript grammar")
    }
}
