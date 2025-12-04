" Language:     MLScript

if exists("b:current_syntax")
  finish
endif

" keywords and constants
syn keyword     mlsKeyword      let set fun val rec mut declare
syn keyword     mlsKeyword      override super new of forall exists
syn keyword     mlsKeyword      class object module pattern trait mixin
syn keyword     mlsKeyword      interface extends namespace type where with
syn keyword     mlsKeyword      break return continue as in out
syn keyword     mlsKeyword      constructor abstract virtual throw
syn keyword     mlsKeyword      case and or enum data
syn keyword     mlsConditional  if then else
syn keyword     mlsRepeat       while for do
syn keyword     mlsExternal     import
syn keyword     mlsExternal     open
syn keyword     mlsConstant     null true false undefined

" number constants
syn match  mlsNumbers     display transparent "\<\d\|\.\d" contains=mlsNumber,mlsNumberError
syn match  mlsNumber      display contained "\(\d\|_\)*\.\=\d*\(e[-+]\=\d\+\)\="

" compiler flags
syn match    mlsFlag           "^:\w\+"

" function names
syn match    mlsCustomFunc     "\w\+\s*(\@="
syn match    mlsCustomFunc     "\w\+\s*\(of\)\@="
syn match    mlsCustomFunc     "\(\.\.\)\@<!\.\@<=\w\+"

" module names
syn match  mlsModuleName  display "\<[A-Z]\+\w*\>"

" operators
syn match    mlsOperator   "+"
syn match    mlsOperator   "*"
syn match    mlsOperator   "/"
syn match    mlsOperator   "|>"
syn match    mlsOperator   "<|"
syn match    mlsOperator   "\.>"
syn match    mlsOperator   "<\."
syn match    mlsOperator   "!>"
syn match    mlsOperator   "<!"
syn match    mlsOperator   "|!"
syn match    mlsOperator   ">>"
syn match    mlsOperator   "<<"
syn match    mlsOperator   "\\"
syn match    mlsOperator   "|\."
syn match    mlsOperator   "|>\."
syn match    mlsOperator   "@"
syn match    mlsOperator   "::"
syn match    mlsOperator   ":::"
syn match    mlsOperator   "++"
syn match    mlsOperator   "\*\*"

" strings
syn region mlsString   start=+"+ end=+"+ skip=+\\\\\|\\"+ contains=mlsSpecial
syn match  mlsSpecial  display contained +\(\\\)\@1<!\(\\\\\)*\zs\\"+

" multiline strings
syn region mlsLongString start=+"""+ end=+"""+ " contains=@Spell

" comments and comment strings
syn keyword  mlsTodo          contained TODO FIXME XXX NOTE
syn region mlsCommentL        start="//" skip="\\$" end="$" keepend contains=mlsTodo
syn region mlsComment         matchgroup=mlsComment start="/\*" end="\*/" contains=mlsTodo

" linking highlight colors
hi link mlsCommentL             Comment
hi link mlsComment              Comment
hi link mlsConditional          Conditional
hi link mlsKeyword              Keyword
hi link mlsRepeat               Repeat
hi link mlsNumber               Number
hi link mlsOperator             Operator
hi link mlsExternal             Include
hi link mlsType                 Type
hi link mlsModuleName           Type
hi link mlsConstant             Constant
hi link mlsString               String
hi link mlsLongString           String
hi link mlsSpecial              SpecialChar
hi link mlsTodo                 Todo
hi link mlsFlag                 Debug
hi link mlsOperator             Operator
hi link mlsCustomFunc           Function
hi link mlsConst                Constant

let b:current_syntax = "mlscript"
