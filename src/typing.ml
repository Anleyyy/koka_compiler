open Typed_ast
open Ast

module Smap = Map.Make(String)
module Imap = Map.Make(Int)

type env = uvaltype * bool Smap.t
(*L'environnement fait correspondre aux variables leur valeur uvaltype
et un booléen qui est vrai si et seulement si la variable est mutable*)
type weakvalenv = uvaltype Imap.t
(*effect list doit être ordonnée selon l'ordre [Enone; Ediv; Econsole; Eall]*)
type postverif = ((uvaltype * loc) list) Imap.t

type total_env = 
  {mutable id : ident;
  mutable weakvalenv : weakvalenv;
  mutable expected_effect : effect list;
  mutable next_weakval : weakval;
  mutable post_verif : postverif;
  mutable return_pile : uvaltype list}

exception Infinite_type of int
exception TypeNotMatching of string
exception FakeTypes of string
exception WrongInput
exception Predefinedf of string

let init_post_verif () =
  let verif90 = Imap.add 90 [] Imap.empty in
  let verif91 = Imap.add 91 [] verif90 in
  let verif11 = Imap.add 11 [] verif91 in
  let verif22 = Imap.add 22 [] verif11 in
  verif22

let f_env = {id = ""; weakvalenv = Imap.empty;
  expected_effect = [Enone; Ediv; Econsole; Eall];
  next_weakval = 0;
  post_verif = init_post_verif ();
  return_pile = []}

let reset_f_env f = 
  f_env.id <- f;
  f_env.weakvalenv <- Imap.empty;
  f_env.expected_effect <- [Enone; Ediv; Econsole; Eall];
  f_env.next_weakval <- 0;
  f_env.post_verif <- init_post_verif ();
  f_env.return_pile <- []

let uvaltype_of weakval = Imap.find weakval f_env.weakvalenv

let assign_uvaltype uv weakval = 
  f_env.weakvalenv <- Imap.add weakval uv f_env.weakvalenv

let add_post_verif number uv loc =
  f_env.post_verif <- Imap.add number ((uv, loc)::(Imap.find number f_env.post_verif)) f_env.post_verif

let new_weakval () = 
  assign_uvaltype (Fixed Vweak) (f_env.next_weakval);
  f_env.next_weakval <- f_env.next_weakval + 1;
  Mutable (f_env.next_weakval - 1)

let rec equal_weakval weakval1 weakval2 =
  if weakval1 = weakval2 then true else
  (match uvaltype_of weakval2 with
  | Mutable w -> 
    if w = weakval1 then true else equal_weakval weakval1 w
  | _ -> false) ||
  (match uvaltype_of weakval1 with
  | Mutable w -> 
    if w = weakval2 then true else equal_weakval w weakval2
  | _ -> false)

let is_predefined_function id = 
  id = "println" || 
  id = "default" || 
  id = "head" || 
  id = "tail" ||
  id = "for" || 
  id = "repeat" || 
  id = "while"

let rec without_effect effect effect_list =
  match effect_list with
  | Enone::s -> Enone::(without_effect effect s)
  | _ ->
    (match effect with
    | Enone -> effect_list
    | Eall -> []
    | Ediv ->
      (match effect_list with
      | Ediv::s -> without_effect effect s
      | Econsole::s -> [Econsole]
      | _ -> [])
    | Econsole ->
      (match effect_list with
      | Ediv::s -> [Ediv]
      | _ -> []))

let with_effect effect0 effect_list =
  let rec rev_with_effect effect rev_effect_list = 
    match rev_effect_list with
    | Eall::s -> Eall::(rev_with_effect effect s)
    | _ ->
      (match effect with
      | Enone -> rev_effect_list
      | Eall -> []
      | Ediv ->
        (match rev_effect_list with
        | Econsole::s -> rev_with_effect effect s
        | Ediv::s -> [Ediv]
        | _ -> [])
      | Econsole ->
        (match rev_effect_list with
        | Econsole::s -> [Econsole]
        | _ -> []))
    in List.rev(rev_with_effect effect0 (List.rev effect_list))

let union_effect effect_list =
  let rec compute_effect remaining_effects current_effect =
    match remaining_effects with
    | [] -> current_effect
    | e::s -> 
      match e with
      | Enone -> compute_effect s current_effect
      | Eall -> Eall
      | Ediv -> if current_effect = Econsole then Eall else compute_effect s Ediv
      | Econsole -> if current_effect = Ediv then Eall else compute_effect s Econsole
  in compute_effect effect_list Enone

let union_ueffect ueffect_list =
  let l = ref [] in
  let fixed = ref true in
  List.iter (fun ueffect -> 
    match ueffect with
    | Efixed effect -> l := effect::!l
    | Emutable effect -> l := effect::!l; fixed := false) ueffect_list;
  if !fixed then Efixed (union_effect !l)
  else Emutable (union_effect !l)

let rec return_ueffect_of_f = function
  | Mutable weakval -> return_ueffect_of_f (uvaltype_of weakval)
  | Fixed (Varrow (_, (e, _))) -> Efixed e
  | Fixed Vweak -> Efixed Enone (*choix arbitraire*)
  | Uarrow (_, (ue, _)) -> ue
  | _ -> raise WrongInput

let rec effect_list_of_ident_list = function
  | [] -> []
  | x::s -> 
    if x = "div" then Ediv::(effect_list_of_ident_list s)
    else if x = "console" then Econsole::(effect_list_of_ident_list s)
    else raise (FakeTypes ("effect " ^ x ^ " is not defined"))

let rec valtype_of_kokatype = function
  | Katype a -> valtype_of_akokatype a
  | Kmonoparam (Akunit, (ident_list, k)) -> valtype_of_kokatype (Kpluriparam ([], (ident_list, k)))
  | Kmonoparam (a, (ident_list, k)) -> 
    let paraml = [valtype_of_akokatype a] in
    let result_effect = union_effect (effect_list_of_ident_list ident_list) in
    let result_valtype = valtype_of_kokatype k in
    Varrow (paraml, (result_effect, result_valtype))
  | Kpluriparam (kl, (ident_list, k)) ->
    let paraml = ref [] in
    List.iter (fun k -> paraml := !paraml @ [valtype_of_kokatype k]) kl;
    let result_effect = union_effect (effect_list_of_ident_list ident_list) in
    let result_valtype = valtype_of_kokatype k in
    Varrow (!paraml, (result_effect, result_valtype))

and valtype_of_akokatype = function
  | Aknoparam id ->
    if id = "unit" then Vunit
    else if id = "bool" then Vbool
    else if id = "int" then Vint
    else if id = "string" then Vstring
    else if id = "list" || id = "maybe" then
      raise (FakeTypes ("type " ^ id ^ " needs an argument : " ^ id ^ "<type>"))
    else raise (FakeTypes ("type " ^ id ^ " is not defined"))
  | Akparam (id, k) ->
    if id = "list" then Vlist (valtype_of_kokatype k)
    else if id = "maybe" then Vmaybe (valtype_of_kokatype k)
    else if id = "unit" || id = "bool" || id = "int" || id = "string" then
      raise (FakeTypes ("type " ^ id ^ " should not have an argument"))
    else raise (FakeTypes ("type " ^ id ^ " is not defined"))
  | Akbracket k -> valtype_of_kokatype k
  | Akunit -> Vunit

let rec unify_valtypes v1 v2 =
  match v1, v2 with
  | Vweak, v | v, Vweak -> v
  | a, b when a = b -> a
  | Vlist new_v1, Vlist new_v2 -> Vlist (unify_valtypes new_v1 new_v2)
  | Vmaybe new_v1, Vmaybe new_v2 -> Vmaybe (unify_valtypes new_v1 new_v2)
  | Varrow (vl1, (e1, new_v1)), Varrow (vl2, (e2, new_v2)) -> 
    if not (e1=e2) then raise (TypeNotMatching "");
    let result = (e1, unify_valtypes new_v1 new_v2) in
    let new_vl = ref [] in
    List.iter2 (fun x y -> new_vl := !new_vl @ [unify_valtypes x y]) vl1 vl2;
    Varrow (!new_vl, result)
  |a,b -> raise (TypeNotMatching ("This expression has type " ^ (valtype_to_string a) ^ " when it should have type " ^ (valtype_to_string b) ^ "."))


let rec unify_uvaltypes ?(reversed = false) uv1 uv2 =
  match uv1, uv2 with
  | Fixed Vweak, uv | uv, Fixed Vweak -> uv
  | Fixed v1, Fixed v2 -> Fixed (unify_valtypes v1 v2)
  | Mutable weakval1, Mutable weakval2 -> 
    if equal_weakval weakval1 weakval2 then 
      Mutable weakval1
    else
      let uv = unify_uvaltypes (uvaltype_of weakval1) (uvaltype_of weakval2) in
      assign_uvaltype uv weakval1;
      assign_uvaltype (Mutable weakval1) weakval2;
      Mutable weakval1
  | Ulist new_uv1, Ulist new_uv2 -> Ulist (unify_uvaltypes new_uv1 new_uv2)
  | Umaybe new_uv1, Umaybe new_uv2 -> Umaybe (unify_uvaltypes new_uv1 new_uv2)
  | Uarrow (uvl1, utyp1), Uarrow (uvl2, utyp2) ->
    let n1, n2 = (List.length uvl1, List.length uvl2) in
    if n1 < n2 then raise (TypeNotMatching "Wrong number of arguments");
    if n1 > n2 then raise (TypeNotMatching "Wrong number of arguments");
    let result = unify_ucalctypes utyp1 utyp2 in
    let new_uvl = ref [] in
    let counter = ref 0 in
    List.iter2 (fun x y -> 
      new_uvl := !new_uvl @ [
      try unify_uvaltypes x y
      with TypeNotMatching o -> 
        raise (TypeNotMatching ((string_of_int !counter)^" "^o))];
      counter := !counter + 1) uvl1 uvl2;
    Uarrow (!new_uvl, result)
  | Mutable weakval, uv ->
    let new_uv = unify_uvaltypes (uvaltype_of weakval) uv in
    assign_uvaltype new_uv weakval;
    Mutable weakval
  | uv, Mutable weakval ->
    let new_uv = unify_uvaltypes uv (uvaltype_of weakval) in
    assign_uvaltype new_uv weakval;
    Mutable weakval
  | _, Fixed _ -> unify_uvaltypes ~reversed:(not reversed) uv2 uv1
  | Fixed (Vlist v), Ulist uv -> Ulist (unify_uvaltypes (Fixed v) uv)
  | Fixed (Vmaybe v), Umaybe uv -> Umaybe (unify_uvaltypes (Fixed v) uv)
  | Fixed (Varrow (vl, (e, v))), Uarrow _ -> 
    let uvl = ref [] in
    List.iter (fun v -> uvl := !uvl @ [Fixed v]) vl;
    let new_uv1 = Uarrow (!uvl, (Efixed e, Fixed v)) in
    unify_uvaltypes new_uv1 uv2
  |a,b -> raise (TypeNotMatching ("This expression has type" ^ (uvaltype_to_string a) ^ " when it should have type " ^ (uvaltype_to_string b) ^ ""))

and unify_ueffects ue1 ue2 =
  (match ue1, ue2 with
  | Efixed e1, Efixed e2 -> 
    if not (e1=e2) then raise (TypeNotMatching "")
  | Efixed e1, Emutable e2 | Emutable e2, Efixed e1 -> 
    let new_expected_effect = 
      (match e1, e2 with
      | Eall, Eall -> f_env.expected_effect
      | Enone, Enone -> without_effect Eall f_env.expected_effect
      | Ediv, Enone -> without_effect Econsole (with_effect Ediv f_env.expected_effect)
      | Econsole, Enone -> without_effect Ediv (with_effect Econsole f_env.expected_effect)
      | Eall, Enone -> with_effect Eall f_env.expected_effect
      | Eall, Ediv -> with_effect Econsole f_env.expected_effect
      | Eall, Econsole -> with_effect Ediv f_env.expected_effect
      | Ediv, Ediv -> without_effect Econsole f_env.expected_effect
      | Econsole, Econsole -> without_effect Ediv f_env.expected_effect
      | _, _ -> raise (TypeNotMatching ""))
    in if new_expected_effect = [] then raise (TypeNotMatching "")
      else f_env.expected_effect <- new_expected_effect
  | Emutable e1, Emutable e2 ->
    let new_expected_effect = 
      (match e1, e2 with
      | Enone, e | e, Enone -> with_effect e f_env.expected_effect
      | Ediv, Econsole | Econsole, Ediv -> with_effect Eall f_env.expected_effect
      | Ediv, Eall | Eall, Ediv -> with_effect Econsole f_env.expected_effect
      | Econsole, Eall | Eall, Econsole -> with_effect Ediv f_env.expected_effect
      | _, _ -> f_env.expected_effect)
    in if new_expected_effect = [] then raise (TypeNotMatching "")
      else f_env.expected_effect <- new_expected_effect);
  union_ueffect [ue1; ue2]

and unify_ucalctypes (ue1, uv1) (ue2, uv2) =
  (unify_ueffects ue1 ue2, unify_uvaltypes uv1 uv2)

let type_predefined_function id uvl =
  let n = List.length uvl in
  let ue = Efixed Enone in (*choix arbitraire*)
  let uv =
    if id = "println" then
      Uarrow ([new_weakval ()], (Efixed Econsole, Fixed Vunit))
    else if id = "default" then
      let uv_param = new_weakval () in
      Uarrow ([Umaybe uv_param; uv_param], (Efixed Enone, uv_param))
    else if id = "head" then
      let uv_param = new_weakval () in
      Uarrow ([Ulist uv_param], (Efixed Enone, Umaybe uv_param))
    else if id = "tail" then
      let uv_param = new_weakval () in
      Uarrow ([Ulist uv_param], (Efixed Enone, Ulist uv_param))
    else if id = "for" then
      (if n <> 3 then 
        raise (Predefinedf ("for takes three arguments but " ^ (string_of_int n) ^ " were given"));
      let return_ue = 
        (try return_ueffect_of_f (List.nth uvl 2) 
        with WrongInput -> raise (Predefinedf "2"))in
      Uarrow ([Fixed Vint; Fixed Vint; Uarrow ([Fixed Vint], (return_ue, Fixed Vunit))], (return_ue, Fixed Vunit)))
    else if id = "repeat" then
      (if n <> 2 then 
        raise (Predefinedf ("repeat takes two arguments but " ^ (string_of_int n) ^ " were given"));
      let return_ue = 
        (try return_ueffect_of_f (List.nth uvl 1) 
        with WrongInput -> raise (Predefinedf "1"))in
      Uarrow ([Fixed Vint; Uarrow ([], (return_ue, Fixed Vunit))], (return_ue, Fixed Vunit)))
    else
      (if n <> 2 then 
        raise (Predefinedf ("while takes two arguments but " ^ (string_of_int n) ^ " were given"));
      let return_ue1 = 
        (try return_ueffect_of_f (List.nth uvl 0) 
        with WrongInput -> raise (Predefinedf "0"))in
      let return_ue2 = 
        (try return_ueffect_of_f (List.nth uvl 1) 
        with WrongInput -> raise (Predefinedf "1"))in
      Uarrow ([Uarrow ([], (return_ue1, Fixed Vbool));
      Uarrow ([], (return_ue2, Fixed Vunit))],
      (union_ueffect [return_ue1; return_ue2; Efixed Ediv], Fixed Vunit))) in

  {a_content = Taident id; a_utyp = (ue, uv); a_typ = (Enone, Vunit)}

let rec type_expr env e = 
  let d, ty = compute_type_expr env e in
  {content = d; utyp = ty; typ = (Enone, Vunit)}

and type_bexpr env bexpr =
  let c, ty = compute_type_bexpr env bexpr in
  {b_content = c; b_utyp = ty; b_typ = (Enone, Vunit)}

and type_atom env atom =
  let c, ty = compute_type_atom env atom in
  {a_content = c; a_utyp = ty; a_typ = (Enone, Vunit)}

and compute_type_expr env e = 
  match e.content with
  (*Règle d'inférence 15*)
  | Eblock [] -> (Teblock [], (Efixed Enone, Fixed Vunit))

  (*Règle d'inférence 16*)
  | Eblock (stmt::[]) -> 
    (match stmt with
    | Sbexpr bexpr -> 
      let tbexpr = type_bexpr env bexpr in
      (Teblock ((Tsbexpr tbexpr)::[]), tbexpr.b_utyp)
    | _ -> failwith "Parser should raise a syntax error")

  (*Règles d'inférence 17 à 19*)
  | Eblock (stmt::s) ->
    (match stmt with
    (*Règle d'inférence 17*)
    | Sbexpr bexpr -> 
      let tbexpr = type_bexpr env bexpr in
      let new_e = {content = Eblock s; loc = e.loc} in
      let ts = type_expr env new_e in
      (match ts.content with
      | Teblock tstmtl -> 
        let ue1, _ = tbexpr.b_utyp in
        let ue2, uv2 = ts.utyp in
        (Teblock ((Tsbexpr tbexpr)::tstmtl), (union_ueffect [ue1; ue2], uv2))
      | _ -> failwith "Impossible case")
    (*Règle d'inférence 18*)
    | Sval (id, e1) -> 
      let te1 = type_expr env e1 in
      let _, uv1 = te1.utyp in
      let new_env = Smap.add id (uv1, false) env in
      let new_e = {content = Eblock s; loc = e.loc} in
      let ts = type_expr new_env new_e in
      (match ts.content with
      | Teblock tstmtl -> 
        let ue1, _ = te1.utyp in
        let ue2, uv2 = ts.utyp in
        (Teblock ((Tsval (id, te1))::tstmtl), (union_ueffect [ue1; ue2], uv2))
      | _ -> failwith "Impossible case")
    (*Règle d'inférence 19*)
    | Svar (id, e1) -> 
      let te1 = type_expr env e1 in
      let _, uv1 = te1.utyp in
      let new_env = Smap.add id (uv1, true) env in
      let new_e = {content = Eblock s; loc = e.loc} in
      let ts = type_expr new_env new_e in
      (match ts.content with
      | Teblock tstmtl -> 
        let ue1, _ = te1.utyp in
        let ue2, uv2 = ts.utyp in
        (Teblock ((Tsvar (id, te1))::tstmtl), (union_ueffect [ue1; ue2], uv2))
      | _ -> failwith "Impossible case"))
  
  | Ebexpr bexpr -> 
    let tbexpr = type_bexpr env bexpr in
    (Tebexpr tbexpr, tbexpr.b_utyp)

and compute_type_bexpr env bexpr =
  match bexpr.b_content with
  | Batom atom -> 
    let tatom = type_atom env atom in
    (Tbatom tatom, tatom.a_utyp)

  (*Règle d'inférence 5*)
  | Bneg new_bexpr -> 
    let tbexpr = type_bexpr env new_bexpr in
    let ue, uv = tbexpr.b_utyp in
    let _ = (try unify_uvaltypes (Fixed Vint) uv
    with TypeNotMatching _ -> raise (Error (new_bexpr.loc, "expression should have type int"))) in
    (Tbneg tbexpr, (ue, Fixed Vint))

  (*Règle d'inférence 7*)
  | Bnot new_bexpr ->
    let tbexpr = type_bexpr env new_bexpr in
    let ue, uv = tbexpr.b_utyp in
    let _ = (try unify_uvaltypes (Fixed Vbool) uv
    with TypeNotMatching _ -> raise (Error (new_bexpr.loc, "expression should have type bool"))) in
    (Tbnot tbexpr, (ue, Fixed Vbool))

  (*Règles d'inférence 6, 8 à 12*)
  | Bbinop (binop, bexpr1, bexpr2) ->
    let tbexpr1 = type_bexpr env bexpr1 in
    let tbexpr2 = type_bexpr env bexpr2 in
    let ue1, uv1 = tbexpr1.b_utyp in
    let ue2, uv2 = tbexpr2.b_utyp in
    (match binop with
    (*Règle d'inférence 6*)
    | Badd | Bsub | Bmul | Bdiv | Bmod ->
      let _ = (try unify_uvaltypes (Fixed Vint) uv1
      with TypeNotMatching _ -> 
        raise (Error (bexpr1.loc, "expression should have type int"))) in
      let _ = (try unify_uvaltypes (Fixed Vint) uv2
      with TypeNotMatching _ -> 
        raise (Error (bexpr2.loc, "expression should have type int"))) in
      (Tbbinop (binop, tbexpr1, tbexpr2), (union_ueffect [ue1; ue2], Fixed Vint))

    (*Règle d'inférence 8*)
    | Blt | Ble | Bgt | Bge ->
      let _ = (try unify_uvaltypes (Fixed Vint) uv1
      with TypeNotMatching _ -> 
        raise (Error (bexpr1.loc, "expression should have type int"))) in
      let _ = (try unify_uvaltypes (Fixed Vint) uv2
      with TypeNotMatching _ -> 
        raise (Error (bexpr2.loc, "expression should have type int"))) in
      (Tbbinop (binop, tbexpr1, tbexpr2), (union_ueffect [ue1; ue2], Fixed Vbool))

    (*Règle d'inférence 9*)
    | Beq | Bneq ->
      let uv = (try unify_uvaltypes uv1 uv2
      with TypeNotMatching o -> 
        raise (Error (bexpr.loc, "types do not match around =="^o))) in
      (if binop = Beq then
        add_post_verif 90 uv bexpr1.loc
      else 
        add_post_verif 91 uv bexpr1.loc);
      (Tbbinop (binop, tbexpr1, tbexpr2), (union_ueffect [ue1; ue2], Fixed Vbool))

    (*Règle d'inférence 10*)
    | Band | Bor ->
      let _ = (try unify_uvaltypes (Fixed Vbool) uv1
      with TypeNotMatching _ -> 
        raise (Error (bexpr1.loc, "expression should have type bool"))) in
      let _ = (try unify_uvaltypes (Fixed Vbool) uv2
      with TypeNotMatching _ -> 
        raise (Error (bexpr2.loc, "expression should have type bool"))) in
      (Tbbinop (binop, tbexpr1, tbexpr2), (union_ueffect [ue1; ue2], Fixed Vbool))

    (*Règle d'inférence 11-12*)
    | Bconcat ->
      let uv = (try unify_uvaltypes uv1 uv2
      with TypeNotMatching o -> 
        raise (Error (bexpr.loc, "types do not match around the operator ++ : "^o^ " Those types should both be string or 'a list"))) in
      add_post_verif 11 uv bexpr1.loc;
      (Tbbinop (binop, tbexpr1, tbexpr2), (union_ueffect [ue1; ue2], uv)))

  (*Règle d'inférence 4*)
  | Bassign (id, new_bexpr) ->
    let tbexpr = type_bexpr env new_bexpr in
    let ue, uv = tbexpr.b_utyp in
    let current_uv, is_var = 
    (try Smap.find id env
    with Not_found -> raise (Error (bexpr.loc, "variable " ^ id ^ " does not exist"))) in
    if is_var then
      let _ = (try unify_uvaltypes uv current_uv
      with TypeNotMatching o -> 
        raise (Error (new_bexpr.loc, "types do not match around :="^o))) in
      (Tbassign (id, tbexpr), (ue, Fixed Vunit))
    else raise (Error (bexpr.loc, "variable " ^ id ^ " is not mutable"))

  (*Règle d'inférence 13*)
  | Bif (e1, e2, e3) ->
    let te1 = type_bexpr env e1 in
    let te2 = type_expr env e2 in
    let te3 = type_expr env e3 in
    let ue1, uv1 = te1.b_utyp in
    let ue2, uv2 = te2.utyp in
    let ue3, uv3 = te3.utyp in
    let _ = (try unify_uvaltypes (Fixed Vbool) uv1
      with TypeNotMatching o -> 
        raise (Error (e1.loc, "this expression should have type bool"))) in
    let uv = (try unify_uvaltypes uv2 uv3
      with TypeNotMatching o -> 
        raise (Error (bexpr.loc, "types do not match around if"^o))) in
    (Tbif (te1, te2, te3), (union_ueffect [ue1; ue2; ue3], uv))

  (*Règles d'inférence 20-21*)
  | Bfn fb -> 
    let uv, new_fb = type_fb bexpr.loc false fb env in
    (match f_env.return_pile with
    | x::s -> (f_env.return_pile <- s)
    | _ -> failwith "Impossible case");
    let result_ueffect = 
      (match uv with Uarrow (_, (x, _)) -> x | _ -> failwith "Impossible case") in
    (Tbfn new_fb, (result_ueffect, uv))

  (*Règle d'inférence 23*)
  | Breturn e -> 
    let te = type_expr env e in
    let ue, uv = te.utyp in
    let _ = (try unify_uvaltypes uv (match f_env.return_pile with x::s -> x | [] -> failwith "Impossible case")
      with TypeNotMatching o -> 
        raise (Error (e.loc, "types do not match after return"^o))) in
    (Tbreturn te, (ue, new_weakval ()))

and compute_type_atom env a = 
  match a.a_content with
  | Aexpr e -> 
    let te = type_expr env e in
    (Taexpr te, te.utyp)

  (*Règle d'inférence 1*)
  | Aunit -> (Taunit, (Efixed Enone, Fixed Vunit))
  | Abool b -> (Tabool b, (Efixed Enone, Fixed Vbool))
  | Astring s -> (Tastring s, (Efixed Enone, Fixed Vstring))
  | Aint i -> (Taint i, (Efixed Enone, Fixed Vint))

  (*Règle d'inférence 2-3*)
  | Aident id ->
    if is_predefined_function id then
        raise (Error (a.loc, "identifier (" ^ id ^ ") cannot be resolved"));
    let uv, _ = 
    (try Smap.find id env
    with Not_found -> raise (Error (a.loc, "no variable or function named " ^ id))) in
    (Taident id, ((if id = f_env.id then Efixed Ediv else Efixed Enone), uv))

  (*Règle d'inférence 22*)
  | Acall (new_a, el) ->
    let is_println_call = ref false in
    let loc_dernier_arg = ref new_a.loc in
    (*new_a est juste une valeur d'initialisation
    pour que le type soit loc ref*)
    let tel = ref [] in
    let uvaltype_list = ref [] in
    let ueffect_list = ref [] in
    let loc_list = ref [] in
    List.iter (fun e -> 
      let te = type_expr env e in
      let te_ue, te_uv = te.utyp in
      loc_dernier_arg := e.loc;
      loc_list := !loc_list @ [e.loc];
      tel := !tel @ [te];
      uvaltype_list := !uvaltype_list @ [te_uv];
      ueffect_list := !ueffect_list @ [te_ue]) el;
    let ta = 
      (match new_a.a_content with
      | (Aident id) when is_predefined_function id -> 
        if id = "println" then is_println_call := true;
        (try type_predefined_function id !uvaltype_list 
        with Predefinedf s -> 
          (match int_of_string_opt s with
          | None -> raise (Error (a.loc, s))
          | Some n -> raise (Error (List.nth !loc_list n, s))))
      | _ -> type_atom env new_a) in
    let ue, uv = ta.a_utyp in

    let expected_uv = Uarrow (!uvaltype_list, (
      (try return_ueffect_of_f uv 
      with WrongInput ->
        raise (Error (new_a.loc, "only functions can be applied"))), new_weakval ())) in
    let rec return_ucalctype_of = function
      | Mutable weakval -> return_ucalctype_of (uvaltype_of weakval)
      | Uarrow (_, x) -> x
      | _ -> failwith "Impossible case" in
    let unified_uv =
      (try 
        unify_uvaltypes expected_uv uv
      with TypeNotMatching s ->
        (let split_on_first_space s =
          try
            let idx = String.index s ' ' in
            let first_part = String.sub s 0 idx in
            let second_part = String.sub s (idx + 1) (String.length s - idx - 1) in
            (first_part, second_part)
          with
          | Not_found -> (s, "") in

        let alpha,o = split_on_first_space s in



          match int_of_string_opt alpha with
        | None -> raise (Error (a.loc, s))
        | Some n -> raise (Error (List.nth !loc_list n, "types do not match on the "^ (string_of_int (n+1)) ^"th argument. "^o)))) in
    let return_ue, return_uv = return_ucalctype_of unified_uv in
    if !is_println_call then add_post_verif 22 return_uv !loc_dernier_arg;
    (Tacall (ta, !tel), (union_ueffect ([ue; return_ue] @ !ueffect_list), return_uv))

  (*Règle d'inférence 14*)
  | Alist el -> 
    let tel = ref [] in
    let uvaltype_list = ref [] in
    let ueffect_list = ref [] in
    let loc_list = ref [] in
    List.iter (fun e -> 
      let te = type_expr env e in
      let ue, uv = te.utyp in
      tel := !tel @ [te];
      loc_list := !loc_list @ [e.loc];
      uvaltype_list := !uvaltype_list @ [uv];
      ueffect_list := !ueffect_list @ [ue]) el;

    let rec unify_uvaltype_list uvl n =
      match uvl with
      | [] -> new_weakval ()
      | x::[] -> x
      | uv1::(uv2::s) -> 
        let uv = (try unify_uvaltypes uv1 uv2
          with TypeNotMatching _ -> 
            raise (Error (List.nth !loc_list n, "types do not match list"))) in unify_uvaltype_list (uv::s) (n+1)
    in 
    let uv = unify_uvaltype_list !uvaltype_list 1 in
    let effect = union_ueffect !ueffect_list in
    (Talist !tel, (effect, Ulist uv))

and uvaltype_to_valtype ?(weakvals = []) = function
  | Mutable weakval -> 
    (match List.find_opt (fun x -> x = weakval) weakvals with
    | None -> uvaltype_to_valtype ~weakvals:(weakval::weakvals) (uvaltype_of weakval)
    | Some x -> raise (Infinite_type x))
  | Fixed valtype -> valtype
  | Ulist uvaltype -> Vlist (uvaltype_to_valtype ~weakvals:weakvals uvaltype)
  | Umaybe uvaltype -> Vmaybe (uvaltype_to_valtype ~weakvals:weakvals uvaltype)
  | Uarrow (uvaltypel, ucalctype) -> 
    let l = ref [] in
    List.iter (fun uvaltype -> l:= [uvaltype_to_valtype ~weakvals:weakvals uvaltype] @ !l) uvaltypel;
    Varrow (!l ,ucalctype_to_calctype ucalctype)

and ueffect_to_effect = function
  | Emutable effect -> 
    let f_effect = 
      match f_env.expected_effect with
      | [] -> failwith "Impossible case"
      | x::s -> x
    in union_effect [f_effect; effect]
  | Efixed effect -> effect

and ucalctype_to_calctype ?(weakvals = []) (ue, uv) = 
  (ueffect_to_effect ue, uvaltype_to_valtype ~weakvals:weakvals uv)

and utyp_to_typ_expr te =
  (*te = {content : te.content; utyp : te.utyp; typ : pas le bon}*)
  let typ = ucalctype_to_calctype te.utyp in
  let new_content = 
  match te.content with 
  | Teblock tstmtl -> 
    let new_tstmtl = ref [] in
    List.iter (fun tstmt -> new_tstmtl := !new_tstmtl @
    (match tstmt with
    | Tsbexpr tbexpr -> [Tsbexpr (utyp_to_typ_bexpr tbexpr)]
    | Tsval (id, texpr) -> [Tsval (id, utyp_to_typ_expr texpr)]
    | Tsvar (id, texpr) -> [Tsvar (id, utyp_to_typ_expr texpr)])) tstmtl;
    Teblock !new_tstmtl
  | Tebexpr tbexpr -> Tebexpr (utyp_to_typ_bexpr tbexpr)
  in
  {content = new_content; utyp = (Efixed Enone, Fixed Vunit); typ = typ}

and utyp_to_typ_bexpr tbexpr =
  (*tbexpr = {b_content : tbexpr.b_content; b_utyp : tbexpr.b_utyp; b_typ : pas le bon}*)
  let typ = ucalctype_to_calctype tbexpr.b_utyp in
  let new_content = 
  match tbexpr.b_content with
  | Tbatom tatom -> Tbatom (utyp_to_typ_atom tatom)
  | Tbneg new_tbexpr -> Tbneg (utyp_to_typ_bexpr new_tbexpr)
  | Tbnot new_tbexpr -> Tbnot (utyp_to_typ_bexpr new_tbexpr)
  | Tbbinop (binop, tbexpr1, tbexpr2) -> 
    Tbbinop (binop, utyp_to_typ_bexpr tbexpr1, utyp_to_typ_bexpr tbexpr2)
  | Tbassign (id, new_tbexpr) -> Tbassign (id, utyp_to_typ_bexpr new_tbexpr)
  | Tbif (new_tbexpr, texpr1, texpr2) -> 
    Tbif (utyp_to_typ_bexpr new_tbexpr, utyp_to_typ_expr texpr1, utyp_to_typ_expr texpr2)
  | Tbfn (paraml, annot, texpr) -> Tbfn (paraml, annot, utyp_to_typ_expr texpr)
  | Tbreturn texpr -> Tbreturn (utyp_to_typ_expr texpr)
  in
  {b_content = new_content; b_utyp = (Efixed Enone, Fixed Vunit); b_typ = typ}

and utyp_to_typ_atom ta =
  (*ta = {a_content : ta.a_content; a_utyp : ta.a_utyp; a_typ : pas le bon}*)
  let typ = ucalctype_to_calctype ta.a_utyp in
  let new_content = 
  match ta.a_content with
  | Taexpr texpr -> Taexpr (utyp_to_typ_expr texpr)
  | Tacall (tatom, texprl) -> 
    let new_texprl = ref [] in
    List.iter (fun texpr -> 
      new_texprl := !new_texprl @ [utyp_to_typ_expr texpr]) texprl;
    Tacall (utyp_to_typ_atom tatom, !new_texprl)
  | Talist texprl ->
    let new_texprl = ref [] in
    List.iter (fun texpr -> 
      new_texprl := !new_texprl @ [utyp_to_typ_expr texpr]) texprl;
    Talist !new_texprl
  | _ -> ta.a_content
  in
  {a_content = new_content; a_utyp = (Efixed Enone, Fixed Vunit); a_typ = typ}

and do_post_verif number = 
  let identifier = 
    if number = 90 then " (==) "
    else if number = 91 then " (!=) "
    else if number = 11 then " (++) "
    else " (println) " in
  if number = 90 || number = 91 then 
    List.iter (fun (uv, loc) ->
    let v = uvaltype_to_valtype uv in
    if v = Vweak then 
      raise (Error (loc, "identifier" ^ identifier ^ "cannot be resolved"))
    else (let _ = 
      try unify_valtypes Vbool v
    with TypeNotMatching _ -> 
      (try unify_valtypes Vint v
    with TypeNotMatching _ -> 
      (try unify_valtypes Vstring v
    with TypeNotMatching _ ->
      raise (Error (loc, "identifier" ^ identifier ^ "cannot be resolved"))))in ())) (Imap.find number f_env.post_verif);
  if number = 11 then 
    List.iter (fun (uv, loc) ->
    let v = uvaltype_to_valtype uv in
    if v = Vweak then 
      raise (Error (loc, "identifier" ^ identifier ^ "cannot be resolved"))
    else (let _ = 
      try unify_valtypes Vstring v
    with TypeNotMatching _ -> 
      (try unify_valtypes (Vlist Vweak) v
    with TypeNotMatching _ -> 
      raise (Error (loc, "identifier" ^ identifier ^ "cannot be resolved"))) in ())) (Imap.find number f_env.post_verif);
  if number = 22 then 
    List.iter (fun (uv, loc) ->
    let v = uvaltype_to_valtype uv in
    if v = Vweak then 
      raise (Error (loc, "identifier" ^ identifier ^ "cannot be resolved"))
    else (let _ = 
      try unify_valtypes Vbool v
    with TypeNotMatching _ -> 
      (try unify_valtypes Vint v
    with TypeNotMatching _ -> 
      (try unify_valtypes Vstring v
    with TypeNotMatching _ ->
      (try unify_valtypes Vunit v
    with TypeNotMatching _ ->
      raise (Error (loc, "identifier" ^ identifier ^ "cannot be resolved"))))) in ())) (Imap.find number f_env.post_verif)

and type_fb loc fun_decl (paraml, annot, e) previous_env = 
  let env = ref Smap.empty in
  let param_uvl = ref [] in
  let f_uv = 
    (try match annot with 
    | Noannot -> new_weakval ()
    | Annot (ident_list, k) -> 
      let uv = new_weakval () in
      let expected_effect = union_effect (effect_list_of_ident_list ident_list) in
      let expected_valtype = valtype_of_kokatype k in
      (if fun_decl then f_env.expected_effect <- [expected_effect]);
      unify_uvaltypes (Fixed expected_valtype) uv 
    with FakeTypes s -> raise (Error (loc, s)))
    in
  f_env.return_pile <- f_uv::f_env.return_pile;
  (try
    List.iter (fun (id, k) -> 
      let param_uv = Fixed (valtype_of_kokatype k) in
      param_uvl := !param_uvl @ [param_uv];
      (match Smap.find_opt id !env with
      | None -> ()
      | Some _ -> raise (Error (loc, id ^ " is already defined")));
      env := Smap.add id (param_uv, false) !env;) paraml
  with FakeTypes s -> raise (Error (loc, s)));
    
  Smap.iter (fun id data -> 
    (match Smap.find_opt id !env with
      | None -> env := Smap.add id data !env
      | Some _ -> ()))

    (if fun_decl then 
      Smap.add f_env.id (Uarrow (!param_uvl, (Emutable Enone, f_uv)), false) previous_env
    else previous_env);
  
  let te = type_expr !env e in
  let result_ueffect, result_uvaltype = te.utyp in
  (if fun_decl then (try
    let _ = List.find (fun x -> x = ueffect_to_effect result_ueffect) f_env.expected_effect in ()
  with
    Not_found -> raise (Error (e.loc, "types do not match wrong effect"))));
  (if not fun_decl then 
    let effect = ueffect_to_effect result_ueffect in
    let expected_effect = 
      (match annot with
      | Noannot -> effect
      | Annot (ident_list, _) -> union_effect (effect_list_of_ident_list ident_list)) in
    if not (expected_effect = effect) then 
      raise (Error (e.loc, "types do not match, wrong effect, the expected effect is " ^ (effect_to_string expected_effect) ^ " and we have " ^ (effect_to_string effect) ^ ".")));
  (try
    let _ = unify_uvaltypes result_uvaltype (f_uv) in ()
  with TypeNotMatching o-> 
    raise (Error (e.loc, "types do not match"^o)));
  let result_ucalctype = (result_ueffect, result_uvaltype) in
  let f_uval = Uarrow (!param_uvl, result_ucalctype) in 
  let new_te = 
    if fun_decl then utyp_to_typ_expr te else te in
  (if fun_decl then 
    do_post_verif 90;
    do_post_verif 91;
    do_post_verif 11;
    do_post_verif 22);
  ((if fun_decl then Fixed (uvaltype_to_valtype (f_uval)) else f_uval), (paraml, annot, new_te))

(* Fonctions de débuggage *)

and print_uv uv =
  let v = uvaltype_to_valtype uv in
  let v_str = Typed_ast.valtype_to_string v in
  Printf.printf "%s\n" v_str

and print_ue ue =
  let e = ueffect_to_effect ue in
  let e_str = Typed_ast.effect_to_string e in
  Printf.printf "%s\n" e_str

and print_te te =
  let te_str = Typed_ast.texpr_to_string te in
  Printf.printf "%s\n" te_str

(* Fonction principale *)
let type_file file = 
  let env = ref Smap.empty in
  let tfile = ref [] in
  let main = ref false in
  List.iter (fun (f, fb, loc) -> 
    (if f = "main" then 
      (main := true;
      let paraml, _, _ = fb in
      if List.length paraml > 0 then 
        raise (Error (loc, "main takes no arguments"))));
    (match Smap.find_opt f !env with
    | None -> ()
    | Some _ -> raise (Error (loc, "definition " ^ f ^ " is already defined in this module")));
    reset_f_env f;
    let (f_uval, tfb) = type_fb loc true fb !env in
    env := Smap.add f (f_uval, false) !env;
    tfile := !tfile @ [(f, tfb)];) file;
  if not !main then 
    raise (GlobalError "Typing error : no function main")
  else
    !tfile
