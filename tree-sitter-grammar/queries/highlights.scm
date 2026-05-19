; Keywords
"let" @keyword
"in" @keyword
"data" @keyword
"effect" @keyword
;"()" @keyword

"=" @operator
"->" @operator
"|" @operator
;"+" @operator
;"-" @operator

; Punctuation
[
;  "]"
;  "["
  "{"
  "}"
  "("
  ")"
] @punctuation.braces

[
  ";"
  ","
  ":"
]@punctuation.delimiter

; Literals
(integer) @number
(string_literal) @string


;Comments
(comment) @comment

; Variables
(variable) @variable

; Definition (let x = ...)
(let_decl name: (variable) @variable.declaration)

; Effect Op definition
;(effect_operation effect_op_name: (variable) @type.definition)

; Data Declarations
; Type constructor "data MyType ..."
;; Type name
(data_decl
  type_name: (type
    (type_constructor
      (upper_ident) @type.definition)))
;; Type parameters
(data_decl
  type_name: (type (type_param) @variable.builtin))

; Data constructors
; data MyType a = One | Two a
;; Constructor name
(data_decl
  cstr_list: (cstr_list
    (type (type_constructor (upper_ident) @type))))

;; Type Parameters
(data_decl
  cstr_list: (cstr_list (_ (type_param) @variable.builtin)))

; Effect Declarations
(effect_decl
  effect_name: (effect_name (type (type_constructor (upper_ident) @type))))

(effect_decl
  effect_name: (effect_name(type (type_param) @variable.builtin)))

(effect_decl (effect_op effect_op_name: (lower_ident) @function))
(effect_decl (effect_op (type (type_param) @type)))
(effect_decl (effect_op (type (type_constructor (upper_ident) @type))))

