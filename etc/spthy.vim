" Vim syntax file
" Language:     DH-proto-proof Security Protocol Theory Files
" Maintainer:   Nick Moore <nicholas.moore@cs.ox.ac.uk>
" Last Change:  2017 06 07
" based on Claudio Fleiner's <claudio@fleiner.com> spthy syntax highlighting
" file.

" Quit when a syntax file was already loaded
if !exists("main_syntax")
  if version < 600
    syntax clear
  elseif exists("b:current_syntax")
    finish
  endif
  " we define it here so that included files can test for it
  let main_syntax='spthy'
  syn region spthyFold start="{" end="}" transparent fold
endif

" don't use standard HiLink, it will not work with included syntax files
if version < 508
  command! -nargs=+ SpthyHiLink hi link <args>
else
  command! -nargs=+ SpthyHiLink hi def link <args>
endif

" some characters that cannot be in a spthy program (outside a string)
" syn match spthyError "[\\@`]"
" syn match spthyError "<<<\|\.\.\|=>\|<>\|||=\|&&=\|[^-]->\|\*\/"
" syn match spthyOK "\.\.\."

syn match spthyLAtom	        ":>"
syn match spthyLAtom	        "--|"
syn match spthyLAtom	        "<:"
syn match spthyLAtom	        ">+>"
syn match spthyLAtom	        ">->"
syn match spthyLAtom	        "="
syn match spthyLAtom	        "@"
syn match spthyLAtom	        "<"
syn match spthyLAtom	        ">"

syn keyword spthyConstr         aenc sdec senc sdec sign verify hashing signing multiset
syn match spthyConstr           "\<h("he=e-1
syn match spthyConstr           "\<sk("he=e-1
syn match spthyConstr           "\<pk("he=e-1
syn match spthyConstr           "\<fr("he=e-1
syn match spthyConstr           "\<pb("he=e-1
syn match spthyConstr           "\<lts("he=e-1
syn match spthyConstr           "*"
syn match spthyConstr           "\^"
syn match spthyConstr           "\<diffie-hellman"
syn match spthyConstr           "\<symmetric-encryption"
syn match spthyConstr           "\<asymmetric-encryption"

syn keyword spthyDecl           axiom restriction equations functions builtins protocol property in let theory begin end subsection section text
syn match spthyDecl             "\<lemma\>"
syn match spthyDecl             "\<exists-trace"
syn match spthyDecl             "\<all-traces"
syn match spthyDecl             "\<enable"
syn match spthyDecl             "\<rule"
syn match spthyDecl             "\<assertions"
syn match spthyDecl             "\<modulo"
syn match spthyDecl             "\<default_rules"
syn match spthyDecl             "\<anb-proto"
syn match spthyDecl             ":"
syn match spthyDecl             "{\*"
syn match spthyDecl             "\*}"
syn match spthyDecl             "\""
syn match spthyDecl             "\d\+\."

syn match spthyTransfer         "->"
syn match spthyTransfer         "<-"
syn match spthyDecl             "-->"
syn match spthyDecl             "--\["
syn match spthyDecl             "\]->"

syn region spthyLiteral          start="'" end="'"

syn keyword spthyAnnot          contained use_induction sources reuse hide_lemma left right
syn region spthyAnnotLemma      matchgroup=spthyDecl start="\<lemma\>" skip="(\s\+\w\+\s*\[|\])" end=":" matchgroup=NONE contains=spthyAnnot

syn match spthyLogicOp          "==>"
syn match spthyLogicOp          "<=>"
syn keyword spthyLogicOp        F T All Ex
syn match spthyLogicOp          "|"
syn match spthyLogicOp          "&"
syn match spthyLogicOp          "\."

" The following cluster contains all spthy groups except the contained ones
syn cluster spthyTop add=spthyLAtom,spthyDecl


" Comments
syn keyword spthyTodo		 contained TODO FIXME XXX
syn region  spthyComment		 start="/\*"  end="\*/" contains=spthyTodo
syn match   spthyLineComment      "//.*" contains=spthyTodo

syn cluster spthyTop add=spthyComment,spthyLineComment

" Strings and constants
" syn match   spthySpecialError     contained "\\."
" syn match   spthySpecialCharError contained "[^']"
" syn match   spthySpecialChar      contained "\\\([4-9]\d\|[0-3]\d\d\|[\"\\'ntbrf]\|u\+\x\{4\}\)"
" syn region  spthyString		start=+"+ end=+"+ end=+$+ contains=spthySpecialChar,spthySpecialError,@Spell
" " next line disabled, it can cause a crash for a long line
" "syn match   spthyStringError	  +"\([^"\\]\|\\.\)*$+
" syn match   spthyCharacter	 "'[^']*'" contains=spthySpecialChar,spthySpecialCharError
" syn match   spthyCharacter	 "'\\''" contains=spthySpecialChar
" syn match   spthyCharacter	 "'[^\\]'"
" syn match   spthyNumber		 "\<\(0[0-7]*\|0[xX]\x\+\|\d\+\)[lL]\=\>"
" syn match   spthyNumber		 "\(\<\d\+\.\d*\|\.\d\+\)\([eE][-+]\=\d\+\)\=[fFdD]\="
" syn match   spthyNumber		 "\<\d\+[eE][-+]\=\d\+[fFdD]\=\>"
" syn match   spthyNumber		 "\<\d\+\([eE][-+]\=\d\+\)\=[fFdD]\>"
"
" " unicode characters
" syn match   spthySpecial "\\u\+\d\{4\}"
"
" syn cluster spthyTop add=spthyString,spthyCharacter,spthyNumber,spthySpecial,spthyStringError

" catch errors caused by wrong parenthesis
" syn region  spthyParenT  transparent matchgroup=spthyParen  start="("  end=")" contains=@spthyTop,spthyParenT1
" syn region  spthyParenT1 transparent matchgroup=spthyParen1 start="(" end=")" contains=@spthyTop,spthyParenT2 contained
" syn region  spthyParenT2 transparent matchgroup=spthyParen2 start="(" end=")" contains=@spthyTop,spthyParenT  contained
" syn match   spthyParenError       ")"
" " catch errors caused by wrong square parenthesis
" syn region  spthyParenT  transparent matchgroup=spthyParen  start="\["  end="\]" contains=@spthyTop,spthyParenT1
" syn region  spthyParenT1 transparent matchgroup=spthyParen1 start="\[" end="\]" contains=@spthyTop,spthyParenT2 contained
" syn region  spthyParenT2 transparent matchgroup=spthyParen2 start="\[" end="\]" contains=@spthyTop,spthyParenT  contained
" syn match   spthyParenError       "\]"
"
" SpthyHiLink spthyParenError       spthyError

if !exists("spthy_minlines")
  let spthy_minlines = 10
endif
exec "syn sync ccomment spthyComment minlines=" . spthy_minlines

" The default highlighting.
if version >= 508 || !exists("did_spthy_syn_inits")
  if version < 508
    let did_spthy_syn_inits = 1
  endif
  SpthyHiLink spthyLAtom		Operator
  SpthyHiLink spthyComment		Comment
  SpthyHiLink spthyDocComment		Comment
  SpthyHiLink spthyLineComment		Comment
  SpthyHiLink spthyError		Error
  SpthyHiLink spthyDecl		        Typedef
  SpthyHiLink spthyTransfer             Typedef
  SpthyHiLink spthyConstr               Function
  SpthyHiLink spthyAnnot                Label
  SpthyHiLink spthyLiteral              String
  SpthyHiLink spthyTODO                 Todo
  SpthyHiLink spthyLogicOp              Boolean
"  SpthyHiLink spthyVarArg               Function
"  SpthyHiLink spthyBraces		Function
"  SpthyHiLink spthyBranch		Conditional
"  SpthyHiLink spthyUserLabelRef		spthyUserLabel
"  SpthyHiLink spthyLabel		Label
"  SpthyHiLink spthyUserLabel		Label
"  SpthyHiLink spthyConditional		Conditional
"  SpthyHiLink spthyRepeat		Repeat
"  SpthyHiLink spthyExceptions		Exception
"  SpthyHiLink spthyAssert		Statement
"  SpthyHiLink spthyStorageClass		StorageClass
"  SpthyHiLink spthyMethodDecl		spthyStorageClass
"  SpthyHiLink spthyClassDecl		spthyStorageClass
"  SpthyHiLink spthyScopeDecl		spthyStorageClass
"  SpthyHiLink spthyBoolean		Boolean
"  SpthyHiLink spthySpecial		Special
"  SpthyHiLink spthySpecialError		Error
"  SpthyHiLink spthySpecialCharError	Error
"  SpthyHiLink spthyString		String
"  SpthyHiLink spthyCharacter		Character
"  SpthyHiLink spthySpecialChar		SpecialChar
"  SpthyHiLink spthyNumber		Number
"  SpthyHiLink spthyStringError		Error
"  SpthyHiLink spthyStatement		Statement
"  SpthyHiLink spthyOperator		Operator
"  SpthyHiLink spthyComment		Comment
"  SpthyHiLink spthyDocComment		Comment
"  SpthyHiLink spthyLineComment		Comment
"  SpthyHiLink spthyConstant		Constant
"  SpthyHiLink spthyTypedef		Typedef
"  SpthyHiLink spthyTodo			Todo
"  SpthyHiLink spthyAnnotation             PreProc
"
"  SpthyHiLink spthyCommentTitle		SpecialComment
"  SpthyHiLink spthyDocTags		Special
"  SpthyHiLink spthyDocParam		Function
"  SpthyHiLink spthyDocSeeTagParam		Function
"  SpthyHiLink spthyCommentStar		spthyComment
"
"  SpthyHiLink spthyType			Type
"  SpthyHiLink spthyExternal		Include
"
"  SpthyHiLink htmlComment		Special
"  SpthyHiLink htmlCommentPart		Special
"  SpthyHiLink spthySpaceError		Error
endif

delcommand SpthyHiLink

let b:current_syntax = "spthy"

if main_syntax == 'spthy'
  unlet main_syntax
endif

let b:spell_options="contained"

" vim: ts=8
