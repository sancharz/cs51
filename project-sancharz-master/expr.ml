(* 
			 CS 51 Final Project
			MiniML -- Expressions
			     Spring 2017
*)

(* Abstract syntax of MiniML expressions *)

type unop =
  | Negate
;;
    
type binop =
  | Plus
  | Minus
  | Times
  | Equals
  | LessThan
;;
      
type expr =
  | Var of varid                         (* variables *)
  | Num of int                           (* integers *)
  | Bool of bool                         (* booleans *)
  | Unop of unop * expr                  (* unary operators *)
  | Binop of binop * expr * expr         (* binary operators *)
  | Conditional of expr * expr * expr    (* if then else *)
  | Fun of varid * expr                  (* function definitions *)
  | Let of varid * expr * expr           (* local naming *)
  | Letrec of varid * expr * expr        (* recursive local naming *)
  | Raise                                (* exceptions *)
  | Unassigned                           (* (temporarily) unassigned *)
  | App of expr * expr                   (* function applications *)
 and varid = string ;;
  
(* Sets of varids *)
module SS = Set.Make (struct
		       type t = varid
		       let compare = String.compare
		     end ) ;;

type varidset = SS.t ;;

(* Test to see if two sets have the same elements (for
    testing purposes) *)
let same_vars = SS.equal;;

(* Generate a set of variable names from a list of strings (for
    testing purposes) *)
let vars_of_list = SS.of_list ;;
  
(* Return a set of the variable names free in [exp] *)
let rec free_vars (exp : expr) : varidset =
  match exp with
  | Var varid -> SS.add varid SS.empty             
  | Num _n -> SS.empty        
  | Bool _b ->   SS.empty       
  | Unop (_u, e) -> free_vars e         
  | Binop (_bin, e1, e2) -> SS.union (free_vars e1) (free_vars e2)
  | Conditional (_e1, e2, e3) -> SS.union (free_vars e2) (free_vars e3)
  | Fun (varid, e) ->  SS.remove varid (free_vars e)          
  | Let (varid, e1, e2) -> SS.union (SS.remove varid (free_vars e2)) 
                          (free_vars e1)
  | Letrec (varid, e1, e2) -> SS.union (SS.remove varid (free_vars e2)) 
                                        (SS.remove varid (free_vars e1))      
  | Raise  -> SS.empty                  
  | Unassigned -> SS.empty                
  | App (e1, e2) -> SS.union (free_vars e1) (free_vars e2)  
  ;;              
  
(* Return a fresh variable, constructed with a running counter a la
    gensym. Assumes no variable names use the prefix "var". *)
let gensym = 
  let ctr = ref 0 in 
  fun( s : string) -> 
    let v = s ^ string_of_int (!ctr) in 
    ctr := !ctr + 1;
    v;;

let new_varname () : varid =
  gensym "new_v";; 
  
(* Substitute [repl] for free occurrences of [var_name] in [exp] *)
let rec subst (var_name : varid) (repl : expr) (exp : expr) : expr =
  match exp with
  | Var x -> if var_name = x then repl else exp                  
  | Num _n -> exp            
  | Bool _b ->  exp          
  | Unop (u, e) -> Unop (u, subst var_name repl e)        
  | Binop (b, e1, e2) -> Binop (b, subst var_name repl e1, 
                                   subst var_name repl e2)
  | Conditional (e1, e2, e3) -> Conditional(e1, subst var_name repl e2, 
                                               subst var_name repl e3)
  | Fun (v, e) ->  if v = var_name then exp 
                   else if (v <> var_name) && (SS.mem v (free_vars repl))
                   then let z = new_varname () in 
                        Fun(z, subst var_name repl (subst v (Var z) e))
                   else Fun(v, subst var_name repl e) 
  | Let (v, e1, e2) ->if v = var_name 
                      then Let (v, subst var_name repl e1, e2)
                      else if (v <> var_name) && (SS.mem v (free_vars repl))
                      then let z = new_varname () in 
                            Let(z, 
                                subst var_name repl e1, 
                                subst var_name repl (subst v (Var z) e2))
                      else Let (v, subst var_name repl e1, 
                                   subst var_name repl e2)                   
  |Letrec (v, e1, e2) -> if v = var_name 
                         then exp
                         else if (v <> var_name) && (SS.mem v (free_vars repl))
                         then let z = new_varname () in 
                            Let(z, 
                                subst var_name repl e1, 
                                subst var_name repl (subst v (Var z) e2))
                          else Let (v, subst var_name repl e1, 
                                       subst var_name repl e2)
  | Raise ->  exp                     
  | Unassigned -> exp                      
  | App (e1, e2) -> App(subst var_name repl e1, subst var_name repl e2)   
  ;;      
  
(* printing helper functions for expressions *)  
let unop_to_string (u : unop) : string =
  match u with 
  | Negate -> "~"
;;

let binop_to_string (b : binop) : string =
  match b with
  | Plus -> " + "
  | Minus -> " - "
  | Times -> " * "
  | Equals -> " = "
  | LessThan -> " < "
;;
    
(* exp_to_string -- Returns a string representation of the expr *)
let rec exp_to_string (exp : expr) : string =
  match exp with 
  | Var v -> v        
  | Num n -> string_of_int n     
  | Bool b -> string_of_bool b      
  | Unop  (u, e)  -> (unop_to_string u) ^ (exp_to_string e)       
  | Binop (bin, e1, e2) -> (exp_to_string e1) ^ 
                           (binop_to_string bin ) ^ 
                           (exp_to_string e2)
  | Conditional (e1, e2, e3) -> "if " ^ (exp_to_string e1) ^ 
                                " then " ^ (exp_to_string e2) ^
                                " else " ^ (exp_to_string e3)
  | Fun (varid , e) -> "fun " ^ varid ^ " -> " ^ (exp_to_string e ) 
  | Let (varid, e1, e2) -> "let " ^ varid ^ " = " ^ (exp_to_string e1)
                          ^ " in " ^ (exp_to_string e2)
  | Letrec  (varid, e1, e2) -> "let rec " ^ varid ^ " = " ^ (exp_to_string e1) 
                                ^ " in " ^ ( exp_to_string e2)                                
  | Raise ->  "Raise"            
  | Unassigned  -> "Unassigned"                         
  | App (e1, e2)  -> (exp_to_string e1) ^ " " ^ 
                      (exp_to_string e2)
  ;;

(* exp_to_abstract_string: Returns a string representation of the abstract
   syntax of the expr *)
let rec exp_to_abstract_string (exp : expr) : string =
  match exp with 
  | Var v -> "Var(" ^ v ^ ")"       
  | Num n -> "Num(" ^ string_of_int n ^ ")"    
  | Bool b -> "Bool(" ^ string_of_bool b ^ ")"     
  | Unop  (u, e)  -> "Unop(" ^ (unop_to_string u) ^ ", " ^ 
                            exp_to_abstract_string e ^ ")"     
  | Binop (bin, e1, e2) -> "Binop(" ^ (binop_to_string bin ) ^ ", " 
                           ^ (exp_to_abstract_string e1) ^ ", "
                           ^ (exp_to_abstract_string e2) ^ ")" 
  | Conditional (e1, e2, e3) -> "Conditional(" ^ (exp_to_abstract_string e1) 
                                ^ ", " ^ (exp_to_abstract_string e2) ^ ", " ^ 
                                (exp_to_abstract_string e3) ^ ")" 
  | Fun (varid , e) -> "Fun(" ^ varid ^ ", " ^ (exp_to_abstract_string e) ^ ")" 
  | Let (varid, e1, e2) -> "Let(" ^ varid ^ ", " ^ (exp_to_abstract_string e1)
                            ^ ", " ^ (exp_to_abstract_string e2) ^ ")" 
  | Letrec  (varid, e1, e2) -> "Letrec(" ^ varid ^ ", " ^ 
                               (exp_to_abstract_string e1) 
                               ^ ", " ^ ( exp_to_abstract_string e2) ^ ")"                              
  | Raise ->  "Raise"            
  | Unassigned -> "Unassigned"                         
  | App (e1, e2)  -> "App(" ^ (exp_to_abstract_string e1) ^ ", " ^ 
                      (exp_to_abstract_string e2) ^ ")" 
  ;;