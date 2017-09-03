open Expr ;;
open Unix ;;
open Printf ;;
open Evaluation ;;
open Env;;
 
 module SS = Set.Make (struct
		       type t = varid
		       let compare = String.compare
		     end ) ;;


exception Timeout ;;
(* empty environment and sets for use in testing*)
let environ = Env.create ();;
let binop_test = SS.add "y" (SS.add "x" SS.empty);;
let fun_test = SS.add "f" (SS.add "x" SS.empty);;

(* Tests for the Module env functions *)

let test_create_extend_lookup () = 
    let en1 = extend (create ()) "x" (ref (Val (Num 6))) in
    let en2 = extend en1 "y" (ref (Val(Num 10))) in 
    let en3 = extend en2 "x" (ref (Val (Num 2))) in 
    assert ( lookup en3 "x" = Val (Num 2)); 
    assert ( lookup en2 "y" = Val (Num 10));
  () 
;;
(* A call to env_to_string also calls value_to string within the
associated helper functions *)
let test_string_env () =
	let en4 = extend (create ()) "x" (ref (Val (Num 12))) in 
	let en5 = extend en4 "y" 
			  (ref (Val (Fun ("x", Binop (Plus, Var "x", Num 5))))) in
	let en6 = extend en5 "z" (ref (Closure (Num 13, environ))) in
	let en7 = extend (create ()) "x" (ref (Val (Num 56))) in 
	assert ( env_to_string en6  = 
		    "[ z -> ( 13,  [] ) ; y -> fun x -> x + 5 ; x -> 12 ; ]");
	assert ( env_to_string en7 =  "[ x -> 56 ; ]");
	()
;;
let test_string_val () = 
	let en = extend (create ()) "x" (ref (Val (Num 57))) in 
	assert ( value_to_string (Val (Num 6)) = "6" );
	assert ( value_to_string (Val (Fun("x", Var "x"))) = "fun x -> x");
	assert ( value_to_string (Closure (Fun("x", Var "x"), en)) = 
		                     "( fun x -> x,  [x -> 57 ; ] )"); 
	()
;;

(* Informative Unit Testing*)
type test =
{ label : string ;
content : bool Lazy.t ;
time : int ;
fail_msg : string } ;;

type status =
| Passed
| Failed of string
| Raised_exn of string
| Timed_out of int

let sigalrm_handler =
	Sys.Signal_handle (fun _ -> raise Timeout) ;;

let timeout (time : int) (delayed : 'a Lazy.t) : 'a =
	let old_behavior =
	Sys.signal Sys.sigalrm sigalrm_handler in
	let reset_sigalrm () =
	ignore (Unix.alarm 0);
	Sys.set_signal Sys.sigalrm old_behavior in
	ignore (Unix.alarm time) ;
	let res = Lazy.force delayed in
	reset_sigalrm (); res ;;

let run_test ({label; time; content; fail_msg} : test)
(continue : string -> status -> unit)
: unit =
	try
		if timeout time content
		then continue label Passed
		else continue label (Failed fail_msg)
	with
	| Timeout -> continue label (Timed_out time)
	| exn -> continue label
	       (Raised_exn (Printexc.to_string exn))

let present label status =
	match status with
	| Passed -> printf "%s: passed\n" label
	| Failed msg -> printf "%s: failed %s\n" label msg
	| Timed_out secs -> printf "%s: timed out in %d\n" label secs
	| Raised_exn msg -> printf "%s: raised %s\n" label msg ;;
	
let report (tests: test list) : unit =
	List.iter (fun test -> run_test test present) tests ;;

let test ?(fail_msg = "evaluation failed") ?(time = 5) label content =
{ label = label;
content = content;
fail_msg = fail_msg;
time = time } ;;

(* there are more similarities between the eval functions, so only
comprehensively test eval_s and then test the points of differences 
and edge cases that specifically apply to eval_d and eval_l*)

let tests =
[ test "eval_s with Var" (lazy ( eval_s (Var "x") environ = Raise) ) ;
  test "eval_s with Num" (lazy( eval_s (Num 5) environ = Num 5) ) ;
  test "eval_s with Bool" (lazy ( eval_s (Bool true) environ = Bool true) ) ;
  test "eval_s with Unop" (lazy (eval_s (Unop(Negate, Num 6)) environ =
  						         Num (-6))) ;
  test "eval_s with Binop(-)" (lazy (eval_s (Binop(Minus, Num 6, Num 5))
  								    environ = Num (1)));
  test "eval_s with Binop(*)" (lazy (eval_s (Binop(Times, Num 6, Num 5))
  									 environ = Num (30))) ;
  test "eval_s with Binop (=)" (lazy (eval_s (Binop(Equals, Num 6, Num 5))
          							 environ = Bool false)) ;
  test "eval_s with Binop (<)" (lazy (eval_s (Binop(LessThan, Num 5, Num 6))
  									 environ = Bool true)) ;
  test "eval_s with Binop(nonints)" (lazy (eval_s (Binop(Plus, Num 6, Var "x"))
                                          environ = Raise)) ;
  test "eval_s with Conditionals" (lazy (eval_s 
  						                (Conditional( Binop(LessThan, Num 2, 
  						                Num 3), Num 2 , Num 3)) 
  									    environ = Num 2));
  test "eval_s with Fun" (lazy (eval_s (Fun ("x", Binop(Plus, Num 6, Var "x")))
                          environ = Fun ("x", Binop(Plus, Num 6, Var "x")))) ;
  test "ev_s Let" (lazy (eval_s (Let("x", Num 5,Binop(Plus, Num 6, Var "x")))
  					    environ = Num 11 )) ;
  test "eval_s with Raise" (lazy ( eval_s Raise environ = Raise) ) ;
  test "eval_s with Unassigned" (lazy ( eval_s Unassigned environ = 
  								 Unassigned) ) ;
  test "eval_s with App" (lazy (eval_s (App(Fun ("x", 
  	                                   Binop(Plus, Num 6, Var "x")), Num 6)) 
                                       environ = Num 12)) ;
  test ("eval_s with Let" ^
  		"(compare with eval_d)") ( lazy (eval_s (Let ("x", Num 1, 
  											   Let ("f", 
  											   Fun("y", 
  											   Binop(Plus , Var "x", Var "y")), 
  											   Let("x", Num(2), 
  											   App(Var "f", Num 3))))) environ
  											   = Num 4) ) ;
  test ("eval_d with Let" ^
  	   "(compare with eval_s)") ( lazy (eval_d (Let ("x", Num 1, 
  											   Let ("f", 
  											   Fun("y", 
  											   Binop(Plus , Var "x", Var "y")), 
  											   Let("x", Num(2), 
  											   App(Var "f", Num 3))))) environ
  											   = Num 5) ) ;
  test "module Env funs create extend and lookup" 
  								(lazy (test_create_extend_lookup () = ())) ;
  test "module Env fun value_to_string" (lazy (test_string_val () = ())) ;
  test "module Env fun value_to_string" (lazy ( test_string_env () = ())) ;
  test "exp_to_abstr_str on Var" (lazy ( exp_to_abstract_string (Var "foo") =
  									    "Var(foo)" ) ) ;
  test "exp_to_abstr_str on Nums" (lazy ( exp_to_abstract_string (Num 5) = 
  										 "Num(5)" ) ) ;
  test "exp_to_abstr_str on Bool" (lazy ( exp_to_abstract_string (Bool true) =
  															"Bool(true)")) ;
  test "exp_to_abstr_str on Unop" (lazy (exp_to_abstract_string 
  								  (Unop ( Negate, Num(5))) = 
  								  "Unop(~, Num(5))")) ;
  test "exp_to_abstr_str on Binop" (lazy ( exp_to_abstract_string 
  								 (Binop(Plus, Num(5), Num(3))) = 
  								 "Binop( + , Num(5), Num(3))")) ;
  test "exp_to_abstr_str on Conditional" (lazy ( exp_to_abstract_string 
  								  (Conditional (Binop(Equals, Num(5), Num(3)), 
   	                               Num 5, Num 3)) = 
                "Conditional(Binop( = , Num(5), Num(3)), Num(5), Num(3))") ) ;
  test "exp_to_abstr_str on Fun" (lazy ( exp_to_abstract_string 
  								 (Fun ("x", Var "x")) = "Fun(x, Var(x))") ) ;
  test "exp_to_abstr_str on Let" (lazy ( exp_to_abstract_string (Let ("f",
  										 Num 5, Binop(Plus, Var "f", Num 6))) = 
   							"Let(f, Num(5), Binop( + , Var(f), Num(6)))")) ;
  test "exp_to_abstr_str on Letrec" (lazy ( exp_to_abstract_string (Letrec("f", 
   								   Fun("x", 
   								   Conditional(Binop(Equals, Var "x", Num 0),
   								   Num 1,
                                   Binop(Times, Var "x", App(Var "f", 
                                   Binop(Minus, Var "x", Num 1))))),
                                   App(Var "f", Num 4))) = 
   "Letrec(f, Fun(x, Conditional(Binop( = , Var(x), Num(0)), Num(1), Binop( * , Var(x), App(Var(f), Binop( - , Var(x), Num(1)))))), App(Var(f), Num(4)))") ) ;
  test "exp_to_abstr_str on Raise" (lazy ( exp_to_abstract_string Raise = 
  										   "Raise")) ;
  test "exp_to_abstr_str on Unassigned" (lazy ( exp_to_abstract_string 
  										Unassigned = "Unassigned") ) ;
  test "exp_to_abstr_str on App" (lazy ( exp_to_abstract_string 
  										(App(Num 3, Num 4)) = 
  										"App(Num(3), Num(4))") ) ;
 (*test "free_vars on Var " (lazy ( free_vars (Var "x") = 
  							SS.add "x" SS.empty)) ;
  test "free_vars on Num" (lazy ( free_vars (Num 5) = SS.empty ) ) ;
  test "free_vars on Raise" (lazy ( free_vars Raise = SS.empty) ) ;
  test "free_vars on Unassigned" (lazy ( free_vars Unassigned = SS.empty) ) ;
  test "free_vars on Fun" (lazy ( free_vars 
  	 					  (Fun("x",Binop(Plus,Var"x",Var "y"))) = 
   		 				   SS.add "y" SS.empty)) ;
  test "free_vars on Unop" (lazy ( free_vars (Unop (Negate, Var "x")) = 
  						 SS.add "x" SS.empty)) ;
  test "free_vars on Binop" (lazy ( SS.compare binop_test 
   		                   (free_vars (Binop(Plus, Var "x", Var "y"))) = 0) ) ;
  test "free_vars on Fun" (lazy ( SS.compare fun_test 
    	                  (free_vars (Fun("y",App(Var "f",
    	                  Binop(Plus,Var "x",Var "y"))))) = 0) ) ;
  test "free_vars on Let" (lazy ( free_vars 
  	  					  (Let("x",Fun("y",Var "x"), Var"x")) = 
    	                  SS.add "x" SS.empty) ) ;
  test "free_vars on Letrec" (lazy ( free_vars (
  	                         Letrec("x", Fun("y",Var "x"),Var"x")) =
  	                         SS.empty)) ; *)
  test "subst on Num" (lazy ( subst "x" (Num 5) (Num 6) = Num 6 ) ) ;
  test "subst on Var_1" (lazy ( subst "x" (Num 5) (Var "x") = Num 5 )) ;
  test "subst on Var_2" (lazy ( subst "x" (Num 5) (Var "y") = Var "y" )) ;
  test "ssubst on Unop" (lazy ( subst "x" (Num 5) (Unop(Negate, Var "x")) = 
    					 Unop(Negate, Num 5))) ;
  test "subst on Binop" (lazy ( subst "x" (Num 5) 
  	             		( Binop( Plus,Var "y" ,Var "x")) = 
    					Binop(Plus, Var "y", Num 5)) ) ;
  test "subst on Let_1" (lazy ( subst "x" (Num 5) 
        	            (Let("x", Binop(Plus, Num 10, Var "x"), Var "x")) = 
        	             Let("x", Binop(Plus, Num 10, Num 5), Var "x")) ) ;
  test "subst on Let_2" (lazy ( subst "x" (Num 5) 
        	            (Let("y", Binop(Plus, Num 10, Var "x"), 
        	            Binop(Plus, Var "x", Var "y"))) = 
        	            Let ("y", Binop (Plus, Num 10, Num 5), 
        	           Binop (Plus, Num 5, Var "y")))) ;
  test "subst on Fun_1" (lazy ( subst "x" (Num 5) 
  	                          (Fun("y", Binop( Plus, Var "x", Num 5))) = 
    					      Fun ("y", Binop ( Plus, Num 5, Num 5)))) ;				   
  test "Fun_2" (lazy ( subst "x" (Num 5) 
  	                 (Fun("x",Binop(Plus, Var "x", Num 5))) = 
    			     (Fun("x",Binop(Plus, Var "x", Num 5)))) ) 
] ;;

report tests;;