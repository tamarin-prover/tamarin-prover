import XCTest
import SwiftTreeSitter
import TreeSitterSpthy

final class TreeSitterSpthyTests: XCTestCase {
    func testCanLoadGrammar() throws {
        let parser = Parser()
        let language = Language(language: tree_sitter_spthy())
        XCTAssertNoThrow(try parser.setLanguage(language),
                         "Error loading Spthy grammar")
    }
}
