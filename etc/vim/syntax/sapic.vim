" Vim syntax file
" Language:     SAPIC format for Applied Pi calculus-style embedding in tamarin
" Maintainer: Robert Künnemann <robert.kuennemann@uni-saarland.de>
" Last Change:  2017 Feb 28
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
  let main_syntax='sapic'
  syn region sapicFold start="{" end="}" transparent fold
endif

" don't use standard HiLink, it will not work with included syntax files
if version < 508
  command! -nargs=+ SpthyHiLink hi link <args>
else
  command! -nargs=+ SpthyHiLink hi def link <args>
endif

" some characters that cannot be in a sapic program (outside a string)
" syn match sapicError "[\\@`]"
" syn match sapicError "<<<\|\.\.\|=>\|<>\|||=\|&&=\|[^-]->\|\*\/"
" syn match sapicOK "\.\.\."

syn match sapicLAtom	        ":>"
syn match sapicLAtom	        "--|"
syn match sapicLAtom	        "<:"
syn match sapicLAtom	        ">+>"
syn match sapicLAtom	        ">->"
syn match sapicLAtom	        "="
syn match sapicLAtom	        "@"
syn match sapicLAtom	        "<"


syn keyword sapicConstr         aenc sdec senc sdec sign verify hashing signing
syn match sapicConstr           "\<h("he=e-1
syn match sapicConstr           "\<sk("he=e-1
syn match sapicConstr           "\<pk("he=e-1
syn match sapicConstr           "\<fr("he=e-1
syn match sapicConstr           "\<pb("he=e-1
syn match sapicConstr           "\<lts("he=e-1
syn match sapicConstr           "*"
syn match sapicConstr           "\^"
syn match sapicConstr           "\<diffie-hellman"
syn match sapicConstr           "\<symmetric-encryption"
syn match sapicConstr           "\<asymmetric-encryption"
syn match sapicConstr           "\<multiset"

syn keyword sapicDecl           axiom lemma equations functions builtins protocol property in let theory begin end subsection section text predicates options
syn match sapicDecl             "\<exists-trace"
syn match sapicDecl             "\<all-traces"
syn match sapicDecl             "\<enable"
syn match sapicDecl             "\<rule"
syn match sapicDecl             "\<assertions"
syn match sapicDecl             "\<modulo"
syn match sapicDecl             "\<default_rules"
syn match sapicDecl             "\<anb-proto"
syn match sapicDecl             ":"
syn match sapicDecl             "{\*"
syn match sapicDecl             "\*}"
syn match sapicDecl             "\""
syn match sapicDecl             "\d\+\."

syn match sapicTransfer         "->"
syn match sapicTransfer         "<-"
syn match sapicDecl             "-->"
syn match sapicDecl             "--\["
syn match sapicDecl             "\]->"

syn keyword sapicTransfer       new in out lookup as in else if lock unlock event insert delete then
syn match sapicTransfer         "||"
syn match sapicTransfer         "!"

syn region sapicLiteral          start="'" end="'"

syn match sapicLogicOp          "==>"
syn match sapicLogicOp          "<=>"
syn keyword sapicLogicOp        F T All Ex
syn match sapicLogicOp          "|"
syn match sapicLogicOp          "&"
syn match sapicLogicOp          "@"
syn match sapicLogicOp          "\."




" The following cluster contains all sapic groups except the contained ones
syn cluster sapicTop add=sapicLAtom,sapicDecl


" Comments
syn keyword sapicTodo		 contained TODO FIXME XXX
syn region  sapicComment		 start="/\*"  end="\*/" contains=sapicTodo
syn match   sapicLineComment      "//.*" contains=sapicTodo

syn cluster sapicTop add=sapicComment,sapicLineComment

" Strings and constants
" syn match   sapicSpecialError     contained "\\."
" syn match   sapicSpecialCharError contained "[^']"
" syn match   sapicSpecialChar      contained "\\\([4-9]\d\|[0-3]\d\d\|[\"\\'ntbrf]\|u\+\x\{4\}\)"
" syn region  sapicString		start=+"+ end=+"+ end=+$+ contains=sapicSpecialChar,sapicSpecialError,@Spell
" " next line disabled, it can cause a crash for a long line
" "syn match   sapicStringError	  +"\([^"\\]\|\\.\)*$+
" syn match   sapicCharacter	 "'[^']*'" contains=sapicSpecialChar,sapicSpecialCharError
" syn match   sapicCharacter	 "'\\''" contains=sapicSpecialChar
" syn match   sapicCharacter	 "'[^\\]'"
" syn match   sapicNumber		 "\<\(0[0-7]*\|0[xX]\x\+\|\d\+\)[lL]\=\>"
" syn match   sapicNumber		 "\(\<\d\+\.\d*\|\.\d\+\)\([eE][-+]\=\d\+\)\=[fFdD]\="
" syn match   sapicNumber		 "\<\d\+[eE][-+]\=\d\+[fFdD]\=\>"
" syn match   sapicNumber		 "\<\d\+\([eE][-+]\=\d\+\)\=[fFdD]\>"
"
" " unicode characters
" syn match   sapicSpecial "\\u\+\d\{4\}"
"
" syn cluster sapicTop add=sapicString,sapicCharacter,sapicNumber,sapicSpecial,sapicStringError

" catch errors caused by wrong parenthesis
" syn region  sapicParenT  transparent matchgroup=sapicParen  start="("  end=")" contains=@sapicTop,sapicParenT1
" syn region  sapicParenT1 transparent matchgroup=sapicParen1 start="(" end=")" contains=@sapicTop,sapicParenT2 contained
" syn region  sapicParenT2 transparent matchgroup=sapicParen2 start="(" end=")" contains=@sapicTop,sapicParenT  contained
" syn match   sapicParenError       ")"
" " catch errors caused by wrong square parenthesis
" syn region  sapicParenT  transparent matchgroup=sapicParen  start="\["  end="\]" contains=@sapicTop,sapicParenT1
" syn region  sapicParenT1 transparent matchgroup=sapicParen1 start="\[" end="\]" contains=@sapicTop,sapicParenT2 contained
" syn region  sapicParenT2 transparent matchgroup=sapicParen2 start="\[" end="\]" contains=@sapicTop,sapicParenT  contained
" syn match   sapicParenError       "\]"
"
" SpthyHiLink sapicParenError       sapicError

if !exists("sapic_minlines")
  let sapic_minlines = 10
endif
exec "syn sync ccomment sapicComment minlines=" . sapic_minlines

" The default highlighting.
if version >= 508 || !exists("did_sapic_syn_inits")
  if version < 508
    let did_sapic_syn_inits = 1
  endif
  SpthyHiLink sapicLAtom		Operator
  SpthyHiLink sapicProc		Operator
  SpthyHiLink sapicComment		Comment
  SpthyHiLink sapicDocComment		Comment
  SpthyHiLink sapicLineComment		Comment
  SpthyHiLink sapicError		Error
  SpthyHiLink sapicDecl		        Typedef
  SpthyHiLink sapicTransfer             Typedef
  SpthyHiLink sapicConstr               Function
  SpthyHiLink sapicLiteral              String
  SpthyHiLink sapicTODO                 Todo
  SpthyHiLink sapicLogicOp              Boolean
"  SpthyHiLink sapicVarArg               Function
"  SpthyHiLink sapicBraces		Function
"  SpthyHiLink sapicBranch		Conditional
"  SpthyHiLink sapicUserLabelRef		sapicUserLabel
"  SpthyHiLink sapicLabel		Label
"  SpthyHiLink sapicUserLabel		Label
"  SpthyHiLink sapicConditional		Conditional
"  SpthyHiLink sapicRepeat		Repeat
"  SpthyHiLink sapicExceptions		Exception
"  SpthyHiLink sapicAssert		Statement
"  SpthyHiLink sapicStorageClass		StorageClass
"  SpthyHiLink sapicMethodDecl		sapicStorageClass
"  SpthyHiLink sapicClassDecl		sapicStorageClass
"  SpthyHiLink sapicScopeDecl		sapicStorageClass
"  SpthyHiLink sapicBoolean		Boolean
"  SpthyHiLink sapicSpecial		Special
"  SpthyHiLink sapicSpecialError		Error
"  SpthyHiLink sapicSpecialCharError	Error
"  SpthyHiLink sapicString		String
"  SpthyHiLink sapicCharacter		Character
"  SpthyHiLink sapicSpecialChar		SpecialChar
"  SpthyHiLink sapicNumber		Number
"  SpthyHiLink sapicStringError		Error
"  SpthyHiLink sapicStatement		Statement
"  SpthyHiLink sapicOperator		Operator
"  SpthyHiLink sapicComment		Comment
"  SpthyHiLink sapicDocComment		Comment
"  SpthyHiLink sapicLineComment		Comment
"  SpthyHiLink sapicConstant		Constant
"  SpthyHiLink sapicTypedef		Typedef
"  SpthyHiLink sapicTodo			Todo
"  SpthyHiLink sapicAnnotation             PreProc
"
"  SpthyHiLink sapicCommentTitle		SpecialComment
"  SpthyHiLink sapicDocTags		Special
"  SpthyHiLink sapicDocParam		Function
"  SpthyHiLink sapicDocSeeTagParam		Function
"  SpthyHiLink sapicCommentStar		sapicComment
"
"  SpthyHiLink sapicType			Type
"  SpthyHiLink sapicExternal		Include
"
"  SpthyHiLink htmlComment		Special
"  SpthyHiLink htmlCommentPart		Special
"  SpthyHiLink sapicSpaceError		Error
endif

delcommand SpthyHiLink

let b:current_syntax = "sapic"

if main_syntax == 'sapic'
  unlet main_syntax
endif

let b:spell_options="contained"

" vim: ts=8
