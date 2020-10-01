type ide = string;;
type exp = Eint of int | Ebool of bool | Den of ide | Prod of exp * exp | Sum of exp * exp | Diff of exp * exp |
	Eq of exp * exp | Minus of exp | IsZero of exp | Or of exp * exp | And of exp * exp | Not of exp |
	Ifthenelse of exp * exp * exp | Let of ide * exp * exp | Fun of ide * exp | FunCall of exp * exp |
	Letrec of ide * exp * exp |
	Dizionario of (ide * exp ) list | Insert of ide * exp * exp | Delete of exp * ide | 
	Hash_key of exp * ide | Iterate of exp * exp | Fold of exp * exp | Filter of ide list * exp ;;

(*ambiente polimorfo*)
type 't env = ide -> 't;;
let emptyenv (v : 't) = function x -> v;;
let applyenv (r : 't env) (i : ide) = r i;;
let bind (r : 't env) (i : ide) (v : 't) = function x -> if x = i then v else applyenv r x;;

(*tipi esprimibili*)
type evT = Int of int | Bool of bool | Unbound | FunVal of evFun | RecFunVal of ide * evFun | DVal of (ide * evT) list 
and evFun = ide * exp * evT env

(*rts*)
(*type checking*)
let typecheck (s : string) (v : evT) : bool = match s with
	"int" -> (match v with
		Int(_) -> true |
		_ -> false) |
	"bool" -> (match v with
		Bool(_) -> true |
		_ -> false) |
	_ -> failwith("not a valid type");;

(*funzioni primitive*)
let prod x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n*u))
	else failwith("Type error");;

let sum x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n+u))
	else failwith("Type error");;

let diff x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n-u))
	else failwith("Type error");;

let eq x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Bool(n=u))
	else failwith("Type error");;

let minus x = if (typecheck "int" x) 
	then (match x with
	   	Int(n) -> Int(-n))
	else failwith("Type error");;

let iszero x = if (typecheck "int" x)
	then (match x with
		Int(n) -> Bool(n=0))
	else failwith("Type error");;

let vel x y = if (typecheck "bool" x) && (typecheck "bool" y)
	then (match (x,y) with
		(Bool(b),Bool(e)) -> (Bool(b||e)))
	else failwith("Type error");;

let et x y = if (typecheck "bool" x) && (typecheck "bool" y)
	then (match (x,y) with
		(Bool(b),Bool(e)) -> Bool(b&&e))
	else failwith("Type error");;

let non x = if (typecheck "bool" x)
	then (match x with
		Bool(true) -> Bool(false) |
		Bool(false) -> Bool(true))
	else failwith("Type error");;

(*interprete*)
let rec eval (e : exp) (r : evT env) : evT = match e with
	Eint n -> Int n |
	Ebool b -> Bool b |
	IsZero a -> iszero (eval a r) |
	Den i -> applyenv r i |
	Eq(a, b) -> eq (eval a r) (eval b r) |
	Prod(a, b) -> prod (eval a r) (eval b r) |
	Sum(a, b) -> sum (eval a r) (eval b r) |
	Diff(a, b) -> diff (eval a r) (eval b r) |
	Minus a -> minus (eval a r) |
	And(a, b) -> et (eval a r) (eval b r) |
	Or(a, b) -> vel (eval a r) (eval b r) |
	Not a -> non (eval a r) |
	Ifthenelse(a, b, c) -> 
		let g = (eval a r) in
			if (typecheck "bool" g) 
				then (if g = Bool(true) then (eval b r) else (eval c r))
				else failwith ("nonboolean guard") |
	Let(i, e1, e2) -> eval e2 (bind r i (eval e1 r)) |
	Fun(i, a) -> FunVal(i, a, r) |
	FunCall(f, eArg) -> 
		let fClosure = (eval f r) in
			(match fClosure with
				FunVal(arg, fBody, fDecEnv) -> 
					eval fBody (bind fDecEnv arg (eval eArg r)) |
				RecFunVal(g, (arg, fBody, fDecEnv)) -> 
					let aVal = (eval eArg r) in
						let rEnv = (bind fDecEnv g fClosure) in
							let aEnv = (bind rEnv arg aVal) in
								eval fBody aEnv |
				_ -> failwith("non functional value")) |
        Letrec(f, funDef, letBody) ->
        		(match funDef with
            		Fun(i, fBody) -> let r1 = (bind r f (RecFunVal(f, (i, fBody, r)))) in
                         			                eval letBody r1 |
            		_ -> failwith("non functional def")) |

		Dizionario(lst) -> DVal(evalList lst r) |   (*funzione che valuta se la lista passata come argomento è un dizionario*)
		
		Insert (k, v, d) -> 											(*valutazione del dizionario, se superata, applica insertseq*)
			let v1= (eval v r) in (match (eval d r) with          
				|DVal dz  -> DVal(insertseq dz k v1) 
				|_ -> failwith ("Not a Dictionary") ) |

		Delete (d, k) -> 												(*valutazione del dizionario, se superata, applica removeseq*)
			(match (eval d r) with
				|DVal dz -> DVal (removeSeq dz k)           
				| _-> failwith("Not a Dictionary") ) | 

		Hash_key(d, k) ->												(*valutazione del dizionario, se superata, applica lookup*)
			(match (eval d r) with
				|DVal dz -> Bool (lookup k dz)                      
				|_ -> failwith("wrong select value")) |

		Iterate (f, d) -> 												(*valutazione del dizionario, se superata, applica applyseq*)
			(match (eval d r) with
				|DVal dz -> DVal (applyseq f dz r)              
				|_ -> failwith("wrong select value")) |

		Fold (f, d) -> let d1 = Iterate(f, d) in 						(*valutazione del dizionario, se superata, applica applysum*)
			(match (eval d1 r) with
				|DVal dz ->   Int (applysum dz r)               
				|_ -> failwith("wrong select value")) |

		Filter(lst, d) ->                                                (*valutazione del dizionario, se superata, applica filterseq*)
			(match (eval d r) with
				|DVal dz -> DVal (filterSeq lst dz)           
				| _-> failwith("Not a Dictionary"))  

		and insertseq (d : (ide * evT) list)  (k : ide)  (v : evT) : (ide * evT) list =				 (*inserisce la coppia (chiave, valore) nel dizionario, se la chiave risulta già presente,*)
			match d with																						(*il valore viene aggiornato*)
				|[] -> [(k,v)]  
				|(id1, val1) :: rest -> if (k = id1) then (id1,v) :: rest  else (id1,val1) :: (insertseq rest k v) 
				|_ -> failwith("wrong dictionary field")

		and removeSeq (d : (ide * evT) list) (k : ide) : (ide * evT) list = 							(*rimuove la chiave k e il valore assegnata ad essa se presente nel dizionario*)
			match d with
				|[] -> []
				|(id1,val1) :: s1 -> if (k = id1) then (removeSeq s1 k) else (id1,val1) :: (removeSeq s1 k)

		and lookup (k : ide) (d : (ide * evT) list) : bool =															(*restituisce true se la chiave k è presente nel dizionario*)
			 match d with
				|[] -> false
				|(id1, val1):: rest -> if (k = id1) then true else (lookup k rest)               
				|_ -> failwith("wrong record field")

		and funcallIt (f:exp) (eArg:evT) (r1:evT env) : evT = let close = (eval f r1) in
				(match close with
					FunVal(arg, fBody, fDecEnv) -> 
						eval fBody (bind fDecEnv arg  eArg ) |    
						RecFunVal(g, (arg, fBody, fDecEnv)) ->                             (*funzione chiamata dalla applyseq, analoga alla funcall apparte il paramentro eArg che risulta già valutato*)  
						let aVal = eArg  in
							let rEnv = (bind fDecEnv g close) in
								let aEnv = (bind rEnv arg aVal) in
									eval fBody aEnv |
					_ -> failwith("non functional value"))

		and applysum (d : (ide * evT) list)  (rd: evT env) : int =     				(*restituisce la somma dei valori di ogni elemento del dizionario*)
			match d with 
				[] -> 0 |
				(k1,Int(val1)) :: rest -> val1 + (applysum rest rd)  |
				_ -> failwith("wrong dictionary list")		

		and applyseq (f : exp) (d : (ide * evT) list)  (rd: evT env) : (ide * evT) list =     				(*applica la funzione f ad ogni elemento del dizionario*)
			match d with 
				[] -> [] |
				(k1,val1) :: rest -> (k1, funcallIt f val1 rd ) :: applyseq f rest rd |
				_ -> failwith("wrong dictionary list")

		and filter (k : ide) (lst : ide list) : bool =									(*restituisce true se la chiave k è presente nel dizionario*)
			match lst with
				|[] -> false
				|x :: rest -> if x = k then true  else filter k rest
				|_->failwith("wrong dictionary list")

		and filterSeq (lst : ide list) (d : (ide * evT) list) : (ide  *  evT) list =  (*restituisce una lista contenente gli elementi filtrati del dizionario*)
			match d with
				|[] -> []
				|(k, v) :: rest -> if (filter k lst) = true then (k, v) :: filterSeq lst rest else filterSeq lst rest
				|_-> failwith("wrong dictionary list")

		and evalList (lst : (ide  *  exp) list) (r : evT env) : (ide  *  evT) list = 				(*valuta ogni elemento della lista per verificare che si tratti di un dizionario*)
			match lst with
				|[] -> []
				|d :: rest -> (match d with
					(k, arg) -> (k, eval arg r) :: evalList rest r |
					_ -> failwith("wrong dictionary list"));;
		
(* =============================  TESTS  ================= *)

(* basico: no let *)
let env0 = emptyenv Unbound;; (*creazione ambiente*)

let d1 = Dizionario ([("mele", Eint 2) ; ("pere", Eint 1)]);; (*creazione dizionario*)

eval d1 env0;; 

eval (Insert("kiwi", (Eint 3), d1)) env0;;  (*aggiunge la nuova chiave con il valore associato ad essa*)
eval (Insert("mele", (Eint 3), d1)) env0;;  (*aggiorna il valore della chiave se essa è già presente nel dizionario*)

eval (Delete(d1, "mele")) env0;; (*rimuove la chiave dal dizionario se presente*)

eval (Hash_key(d1, "mele")) env0;; (*restituisce true se la chiave è presente nel dizionario, false altrimenti*)

eval (Iterate ((Fun("y", Sum(Den "y", Eint 100))), d1)) env0;;  (*applica Fun ad ogni elemento del dizionario*)

eval (Fold ((Fun("y", Sum(Den "y", Eint 100))), d1)) env0;; (*restituisce la somma dei valori dopo aver applicato Fun ad ogni elemento del dizionario*)

eval(Filter(["mele"], d1)) env0;; (*restituisce il dizionario filtrato eliminando le coppie 
chiave-valore non presenti nella lista delle chiavi passata come parametro*)

