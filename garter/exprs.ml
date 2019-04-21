open Printf


type tag = int
type sourcespan = (Lexing.position * Lexing.position)

type prim1 =
  | Add1
  | Sub1
  | Print
  | PrintB
  | IsBool
  | IsNum
  | IsTuple
  | Not
  | PrintStack

type prim2 =
  | Plus
  | Minus
  | Times
  | And
  | Or
  | Greater
  | GreaterEq
  | Less
  | LessEq
  | Eq
  | EqB


and 'a typ =
  | TyBlank of 'a
  | TyCon of string * 'a
  | TyVar of string * 'a
  | TyArr of 'a typ list * 'a typ * 'a
  | TyApp of 'a typ * 'a typ list * 'a
  | TyTup of 'a typ list * 'a
  | TyClass of string * 'a bind list * 'a bind list * 'a 

and 'a scheme =
  | SForall of string list * 'a typ * 'a

and 'a bind =
  | BBlank of 'a typ * 'a
  | BName of string * 'a typ * 'a
  | BTuple of 'a bind list * 'a (* unwrapping tuples *)

and 'a binding = ('a bind * 'a expr * 'a)

and 'a expr =
  | ESeq of 'a expr * 'a expr * 'a
  | ETuple of 'a expr list * 'a
  | EGetItem of 'a expr * int * int * 'a
  | ESetItem of 'a expr * int * int * 'a expr * 'a
  | ELet of 'a binding list * 'a expr * 'a
  | ELetRec of 'a binding list * 'a expr * 'a
  | EPrim1 of prim1 * 'a expr * 'a
  | EPrim2 of prim2 * 'a expr * 'a expr * 'a
  | EIf of 'a expr * 'a expr * 'a expr * 'a
  | ENumber of int * 'a
  | EBool of bool * 'a
  | ENil of 'a typ * 'a
  | EId of string * 'a
  | EApp of 'a expr * 'a expr list * 'a
  | ELambda of 'a bind list * 'a expr * 'a
  | EAnnot of 'a expr * 'a typ * 'a
  | EDot of 'a expr * string * 'a (* Accessing field on a class object *)
  | EDotApp of 'a expr * string * 'a expr list * 'a (* Calling method from a class object x.foo() x.foo(1, 2, 3) *)
  | EDotSet of 'a expr * string * 'a expr * 'a (* Mutating fields on a class object *)
  | ENew of string * 'a

type 'a decl =
  | DFun of string * 'a bind list * 'a scheme * 'a expr * 'a

type 'a tydecl =
  | TyDecl of string * 'a typ list * 'a

type 'a classdecl =
  | Class of string * string option *  'a bind list * 'a decl list * 'a

type 'a program =
  | Program of 'a tydecl list * 'a classdecl list * 'a decl list list * 'a expr * 'a

type 'a immexpr = (* immediate expressions *)
  | ImmNum of int * 'a
  | ImmBool of bool * 'a
  | ImmId of string * 'a
  | ImmNil of 'a
and 'a cexpr = (* compound expressions *)
  | CIf of 'a immexpr * 'a aexpr * 'a aexpr * 'a
  | CPrim1 of prim1 * 'a immexpr * 'a
  | CPrim2 of prim2 * 'a immexpr * 'a immexpr * 'a
  | CApp of 'a immexpr * 'a immexpr list * 'a
  | CImmExpr of 'a immexpr (* for when you just need an immediate value *)
  | CTuple of 'a immexpr list * 'a
  | CGetItem of 'a immexpr * int * 'a
  | CSetItem of 'a immexpr * int * 'a immexpr * 'a
  | CLambda of string list * 'a aexpr * 'a
  | CNew of string * 'a
  | CDot of 'a immexpr * string * int * 'a (* keeping the offset only *)
  | CDotApp of 'a immexpr * string * int * 'a immexpr list * 'a
  | CDotSet of 'a immexpr * string * int * 'a immexpr * 'a
and 'a aexpr = (* anf expressions *)
  | ASeq of 'a cexpr * 'a aexpr * 'a
  | ALet of string * 'a cexpr * 'a aexpr * 'a
  | ALetRec of (string * 'a cexpr) list * 'a aexpr * 'a
  | ACExpr of 'a cexpr

and 'a adecl =
  | ADFun of string * string list * 'a aexpr * 'a

and 'a aclassdecl =
  | AClass of string * string option *  string list * 'a adecl list * 'a

and 'a aprogram =
  | AProgram of 'a aclassdecl list * 'a adecl list * 'a aexpr * 'a
;;

let rec bind_to_typ bind =
  match bind with
  | BBlank(t, _) -> t
  | BName(_, t, _) -> t
  | BTuple(args, a) -> TyTup(List.map bind_to_typ args, a)
;;


let rec map_tag_E (f : 'a -> 'b) (e : 'a expr) =
  match e with
  | ESeq(e1, e2, a) -> ESeq(map_tag_E f e1, map_tag_E f e2, f a)
  | ETuple(exprs, a) -> ETuple(List.map (map_tag_E f) exprs, f a)
  | EGetItem(e, idx, len, a) -> EGetItem(map_tag_E f e, idx, len, f a)
  | ESetItem(e, idx, len, newval, a) -> ESetItem(map_tag_E f e, idx, len, map_tag_E f newval, f a)
  | EId(x, a) -> EId(x, f a)
  | ENumber(n, a) -> ENumber(n, f a)
  | EBool(b, a) -> EBool(b, f a)
  | ENil(t, a) -> ENil(map_tag_T f t, f a)
  | EAnnot(e, t, a) -> EAnnot(map_tag_E f e, map_tag_T f t, f a)
  | EPrim1(op, e, a) ->
     let tag_prim = f a in
     EPrim1(op, map_tag_E f e, tag_prim)
  | EPrim2(op, e1, e2, a) ->
     let tag_prim = f a in
     let tag_e1 = map_tag_E f e1 in
     let tag_e2 = map_tag_E f e2 in
     EPrim2(op, tag_e1, tag_e2, tag_prim)
  | ELet(binds, body, a) ->
     let tag_let = f a in
     let tag_binding (b, e, t) =
       let tag_bind = f t in
       let tag_b = map_tag_B f b in
       let tag_e = map_tag_E f e in
       (tag_b, tag_e, tag_bind) in
     let tag_binds = List.map tag_binding binds in
     let tag_body = map_tag_E f body in
     ELet(tag_binds, tag_body, tag_let)
  | ELetRec(binds, body, a) ->
     let tag_let = f a in
     let tag_binding (b, e, t) =
       let tag_bind = f t in
       let tag_b = map_tag_B f b in
       let tag_e = map_tag_E f e in
       (tag_b, tag_e, tag_bind) in
     let tag_binds = List.map tag_binding binds in
     let tag_body = map_tag_E f body in
     ELetRec(tag_binds, tag_body, tag_let)
  | EIf(cond, thn, els, a) ->
     let tag_if = f a in
     let tag_cond = map_tag_E f cond in
     let tag_thn = map_tag_E f thn in
     let tag_els = map_tag_E f els in
     EIf(tag_cond, tag_thn, tag_els, tag_if)
  | EApp(name, args, a) ->
     let tag_app = f a in
     EApp(map_tag_E f name, List.map (map_tag_E f) args, tag_app)
  | ELambda(binds, body, a) ->
     let tag_lam = f a in
     ELambda(List.map (map_tag_B f) binds, map_tag_E f body, tag_lam)
 | EDot(expr, id, a) ->
     EDot(map_tag_E f expr, id, f a)
 | EDotApp(expr, id, args, a) ->
     EDotApp(map_tag_E f expr, id, (List.map (fun arg -> (map_tag_E f arg)) args),  f a)
 | EDotSet(expr, id, new_value, a) ->
     EDotSet(map_tag_E f expr, id, map_tag_E f new_value, f a)
 | ENew(class_name, a) ->
     ENew(class_name, f a)

and map_tag_B (f : 'a -> 'b) b =
  match b with
  | BBlank(t, tag) -> BBlank(map_tag_T f t, f tag)
  | BName(x, t, ax) ->
     let tag_ax = f ax in
     let tag_t = map_tag_T f t in
     BName(x, tag_t, tag_ax)
  | BTuple(binds, t) ->
     let tag_tup = f t in
     BTuple(List.map (map_tag_B f) binds, tag_tup)
and map_tag_T (f : 'a -> 'b) t =
  match t with
  | TyBlank a -> TyBlank(f a)
  | TyCon(name, a) -> TyCon(name, f a)
  | TyArr(args, ret, a) ->
     let tag_arrow = f a in
     let tag_args = List.map (map_tag_T f) args in
     let tag_ret = map_tag_T f ret in
     TyArr(tag_args, tag_ret, tag_arrow)
  | TyApp(t, args, a) ->
     let tag_app = f a in
     let tag_t = map_tag_T f t in
     let tag_args = List.map (map_tag_T f) args in
     TyApp(tag_t, tag_args, tag_app)
  | TyVar (x, a) -> TyVar(x, f a)
  | TyTup(tys, a) -> TyTup(List.map (map_tag_T f) tys, f a)
  | TyClass(name, fields, methods, a) -> TyClass(name, List.map (map_tag_B f) fields, List.map (map_tag_B f) methods, f a)
and map_tag_S (f : 'a -> 'b) s =
  match s with
  | SForall(vars, typ, a) -> SForall(vars, map_tag_T f typ, f a)
and map_tag_D (f : 'a -> 'b) d =
  match d with
  | DFun(name, args, scheme, body, a) ->
     let tag_fun = f a in
     let tag_args = List.map (map_tag_B f) args in
     let tag_scheme = map_tag_S f scheme in
     let tag_body = map_tag_E f body in
     DFun(name, tag_args, tag_scheme, tag_body, tag_fun)
and map_tag_TD (f : 'a -> 'b) td =
  match td with
  | TyDecl(name, args, a) ->
     let tag_a = f a in
     TyDecl(name, List.map (map_tag_T f) args, tag_a)
and map_tag_K (f : 'a -> 'b) cl =
  match cl with
  | Class(name, base, fields, decls, a) ->
    Class(name, base, List.map (map_tag_B f) fields, List.map (map_tag_D f) decls, f a)
and map_tag_P (f : 'a -> 'b) p =
  match p with
  | Program(tydecls, classdecls, declgroups, body, a) ->
     let tag_a = f a in
     let tag_tydecls = List.map (map_tag_TD f) tydecls in
     let tag_classdecls = List.map (map_tag_K f) classdecls in
     let tag_decls = List.map (fun group -> List.map (map_tag_D f) group) declgroups in
     let tag_body = map_tag_E f body in
     Program(tag_tydecls, tag_classdecls ,tag_decls, tag_body, tag_a)

let tag (p : 'a program) : tag program =
  let next = ref 0 in
  let tag _ =
    next := !next + 1;
    !next in
  map_tag_P tag p
;;


let combine_tags (f1 : 'a -> 'b) (f2 : 'a -> 'c) (p : 'a program) : ('b * 'c) program =
  map_tag_P (fun a -> (f1 a, f2 a)) p
;;
let tag_and_map (f : 'a -> 'b) (p : 'a program) : ('a * 'b) program =
  map_tag_P (fun a -> (a, f a)) p
;;
let prog_and_tag (p : 'a program) : ('a * tag) program =
  let next = ref 0 in
  let tag _ =
    next := !next + 1;
    !next in
  tag_and_map tag p
;;

let rec untagP (p : 'a program) : unit program =
  match p with
  | Program(tydecls, classdecls, decls, body, _) ->
     Program(List.map untagTD tydecls, List.map untagClass classdecls ,List.map (fun group -> List.map untagD group) decls, untagE body, ())
and untagClass c =
  match c with
  | Class(name, basename, fields, methods, _) ->
       Class(name, basename, fields, List.map untagD methods, ())
and untagE e =
  match e with
  | ESeq(e1, e2, _) -> ESeq(untagE e1, untagE e2, ())
  | ETuple(exprs, _) -> ETuple(List.map untagE exprs, ())
  | EGetItem(e, idx, len, _) -> EGetItem(untagE e, idx, len, ())
  | ESetItem(e, idx, len, newval, _) -> ESetItem(untagE e, idx, len, untagE newval, ())
  | EId(x, _) -> EId(x, ())
  | ENumber(n, _) -> ENumber(n, ())
  | EBool(b, _) -> EBool(b, ())
  | ENil(t, _) -> ENil(untagT t, ())
  | EAnnot(e, t, _) -> EAnnot(untagE e, untagT t, ())
  | EPrim1(op, e, _) ->
     EPrim1(op, untagE e, ())
  | EPrim2(op, e1, e2, _) ->
     EPrim2(op, untagE e1, untagE e2, ())
  | ELet(binds, body, _) ->
     ELet(List.map (fun (b, e, _) -> (untagB b, untagE e, ())) binds, untagE body, ())
  | ELetRec(binds, body, _) ->
     ELetRec(List.map (fun (b, e, _) -> (untagB b, untagE e, ())) binds, untagE body, ())
  | EIf(cond, thn, els, _) ->
     EIf(untagE cond, untagE thn, untagE els, ())
  | EApp(name, args, _) ->
     EApp(untagE name, List.map untagE args, ())
  | ELambda(binds, body, _) ->
     ELambda(List.map untagB binds, untagE body, ())
  | EDot(expr, id, _) ->
      EDot(untagE expr, id, ())
  | EDotApp(expr, id, args, a) ->
      EDotApp(untagE expr, id, (List.map untagE args), ())
  | EDotSet(expr, id, new_value, _) ->
      EDotSet(untagE expr, id, untagE new_value, ())
  | ENew(class_name, _) ->
      ENew(class_name, ())
and untagB b =
  match b with
  | BBlank(typ, _) -> BBlank(untagT typ, ())
  | BName(x, typ, _) -> BName(x, untagT typ, ())
  | BTuple(binds, _) -> BTuple(List.map untagB binds, ())
and untagT t =
  match t with
  | TyBlank _ -> TyBlank ()
  | TyCon(name, _) -> TyCon(name, ())
  | TyArr(args, ret, _) -> TyArr(List.map untagT args, untagT ret, ())
  | TyApp(t, args, _) -> TyApp(untagT t, List.map untagT args, ())
  | TyVar(x, _) -> TyVar(x, ())
  | TyTup(tys, _) -> TyTup(List.map untagT tys, ())
and untagS s =
  match s with
  | SForall(vars, typ, _) -> SForall(vars, untagT typ, ())
and untagD d =
  match d with
  | DFun(name, args, scheme, body, _) ->
     DFun(name, List.map untagB args, untagS scheme, untagE body, ())
and untagTD td =
  match td with
  | TyDecl(name, args, _) -> TyDecl(name, List.map untagT args, ())
;;

let atag (p : 'a aprogram) : tag aprogram =
  let next = ref 0 in
  let tag () =
    next := !next + 1;
    !next in
  let rec helpA (e : 'a aexpr) : tag aexpr =
    match e with
    | ASeq(e1, e2, _) ->
       let seq_tag = tag() in
       ASeq(helpC e1, helpA e2, seq_tag)
    | ALet(x, c, b, _) ->
       let let_tag = tag() in
       ALet(x, helpC c, helpA b, let_tag)
    | ALetRec(binds, body, _) ->
       let letrec_tag = tag() in
       ALetRec(List.map (fun (x, c) -> (x, helpC c)) binds, helpA body, letrec_tag)
    | ACExpr c -> ACExpr (helpC c)
  and helpC (c : 'a cexpr) : tag cexpr =
    match c with
    | CPrim1(op, e, _) ->
       let prim_tag = tag() in
       CPrim1(op, helpI e, prim_tag)
    | CPrim2(op, e1, e2, _) ->
       let prim_tag = tag() in
       CPrim2(op, helpI e1, helpI e2, prim_tag)
    | CIf(cond, thn, els, _) ->
       let if_tag = tag() in
       CIf(helpI cond, helpA thn, helpA els, if_tag)
    | CApp(fn, args, _) ->
       let app_tag = tag() in
       CApp(helpI fn, List.map helpI args, app_tag)
    | CImmExpr i -> CImmExpr (helpI i)
    | CTuple(es, _) ->
       let tup_tag = tag() in
       CTuple(List.map helpI es, tup_tag)
    | CGetItem(e, idx, _) ->
       let get_tag = tag() in
       CGetItem(helpI e, idx, get_tag)
    | CSetItem(e, idx, newval, _) ->
       let set_tag = tag() in
       CSetItem(helpI e, idx, helpI newval, set_tag)
    | CLambda(args, body, _) ->
       let lam_tag = tag() in
       CLambda(args, helpA body, lam_tag)
    | CDot(expr, id, idx,  _) ->
       let dot_tag = tag() in
       CDot(helpI expr, id, idx, dot_tag)
    | CDotApp(expr, id, idx, args,  _) ->
        let dotapp_tag = tag() in
        CDotApp(helpI expr, id, idx, List.map helpI args, dotapp_tag)
    | CDotSet(expr, id, idx, new_value, _) ->
      let dot_set_tag = tag() in
      CDotSet(helpI expr, id, idx, helpI new_value, dot_set_tag)
    | CNew(class_name, _) ->
      let new_class_tag = tag() in
      CNew(class_name, new_class_tag)
  and helpI (i : 'a immexpr) : tag immexpr =
    match i with
    | ImmNil(_) -> ImmNil(tag())
    | ImmId(x, _) -> ImmId(x, tag())
    | ImmNum(n, _) -> ImmNum(n, tag())
    | ImmBool(b, _) -> ImmBool(b, tag())
  and helpD d =
    match d with
    | ADFun(name, args, body, _) ->
       let fun_tag = tag() in
       ADFun(name, args, helpA body, fun_tag)
  and helpClass c =
    match c with
    | AClass(name, basename, fields, methods, _) ->
       let class_tag = tag() in
       AClass(name, basename, fields, List.map helpD methods, class_tag)
  and helpP p =
    match p with
    | AProgram(classdecls, decls, body, _) ->
       AProgram(List.map helpClass classdecls, List.map helpD decls, helpA body, 0)
  in helpP p
