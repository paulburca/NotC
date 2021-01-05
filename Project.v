Require Import Strings.String.
Require Import Strings.Ascii.
Require Import Coq.ZArith.BinInt.
Require Import Lists.List.
Require Export BinNums.
Require Import BinPos BinNat.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.

Inductive NatType :=
  | error_nat : NatType
  | num :  nat -> NatType.

Inductive IntType :=
  | error_int : IntType
  | nr : Z -> IntType.

Inductive BoolType :=
  | error_bool : BoolType
  | boolean : bool -> BoolType.

Inductive StringType :=
  | error_string : StringType
  | strval : string -> StringType.

Coercion boolean: bool >-> BoolType.
Coercion nr : Z >-> IntType.
Coercion num : nat >-> NatType.
Notation "string( S )" := (strval S).
Notation "nat( N )" := (num N).
Notation "int( I )" := (nr I).
Notation "bool( B )" := (boolean B).


Inductive STREXP := 
| svar : string -> STREXP
| sconst: StringType -> STREXP
| strcat : string -> string -> STREXP
| get_vval_s : string -> nat -> STREXP
| to_string : string -> STREXP.

Notation "strcat( A , B )" := (strcat A B)(at level 52).
Notation "strcpy( A , B )" := (strcat A B)(at level 52).

Coercion sconst: StringType >-> STREXP.
Coercion svar: string >-> STREXP.

Fixpoint vect_s_parse (n : nat) (l: list StringType) (default : StringType):string:=
match n,l with
| O, x::l' =>  match x with
              | error_string => ""
              | strval s' => s'
              end
| O, other => match default with
              | error_string => ""
              | strval s' => s'
              end
| S m, nil =>  match default with
              | error_string => ""
              | strval s' => s'
              end
| S m, x::l' => vect_s_parse m l' default
end.

Inductive AExp :=
| avar: string -> AExp
| anum: NatType -> AExp
| aint: IntType -> AExp
| aplus: AExp -> AExp -> AExp
| asub: AExp -> AExp -> AExp
| amul: AExp -> AExp -> AExp
| adiv: AExp -> AExp -> AExp
| amod: AExp -> AExp -> AExp
| apow: AExp -> AExp -> AExp
| to_nat: string -> AExp 
| to_int: string -> AExp
| get_vval_a : string -> nat -> AExp
| strlen: string -> AExp.

Coercion anum : NatType >-> AExp.
Coercion avar : string >-> AExp.
Coercion aint : IntType >-> AExp.

Notation "A +' B" := (aplus A B) (at level 48).
Notation "A -' B" := (asub A B) (at level 48).
Notation "A *' B" := (amul A B) (at level 46).
Notation "A /' B" := (adiv A B) (at level 46).
Notation "A %' B" := (amod A B) (at level 46).
Notation "A ^' B" := (apow A B) (at level 46).

Inductive BExp :=
| btrue : BExp
| bfalse : BExp
| bvar : string -> BExp
| bval : BoolType -> BExp
| blessthan : AExp -> AExp -> BExp
| bnot : BExp -> BExp
| band : BExp -> BExp -> BExp
| bgreaterthan: AExp -> AExp -> BExp
| bor : BExp -> BExp -> BExp
| bxor : BExp -> BExp -> BExp
| bxand : BExp -> BExp -> BExp
| strcmp : STREXP -> STREXP -> BExp
| blet : AExp -> AExp -> BExp
| bget : AExp -> AExp -> BExp
| beq : AExp -> AExp -> BExp
| bneq : AExp -> AExp -> BExp
| get_vval_b : string -> nat -> BExp
| to_bool : string -> BExp.

Coercion bvar: string >-> BExp.
Coercion bval: BoolType >-> BExp.

Notation "A <' B" := (blessthan A B) (at level 53).
Notation "A >' B" := (bgreaterthan A B) (at level 53).
Notation "A <=' B" := (blet A B) (at level 53).
Notation "A >=' B" := (bget A B) (at level 53).
Notation "` A " := (bnot A) (at level 40).
Notation "A &&' B" := (band A B) (at level 55).
Notation "A ||' B" := (bor A B) (at level 55).
Notation "A 'xor'' B" := (bxor A B) (at level 55).
Notation "A 'xand'' B" := (bxand A B) (at level 55).
Notation "A ==' B" := (beq A B) (at level 53).
Notation "A !=' B" := (bneq A B) (at level 53).
Notation "strcmp( A ; B )" := (strcmp A B) (at level 52).


Inductive vect :=
| error_vect: vect
| vector_int : nat -> list IntType -> vect
| vector_nat : nat -> list NatType -> vect
| vector_bool : nat -> list BoolType -> vect
| vector_str : nat -> list StringType -> vect.

Inductive Stmt :=
| def_nat : string -> AExp ->Stmt
| def_bool : string -> BExp -> Stmt
| def_int : string -> AExp -> Stmt
| def_string : string -> STREXP -> Stmt
| def_nat0 : string ->Stmt
| def_bool0 : string -> Stmt
| def_int0 : string  -> Stmt
| def_string0 : string -> Stmt
| def_vector : string -> vect -> Stmt
| assignment : string -> AExp -> Stmt
| bassignment : string -> BExp -> Stmt
| sassignment : string -> STREXP -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt
| dowhile : Stmt -> BExp -> Stmt
| ifthen : BExp -> Stmt -> Stmt
| ifthenelse : BExp -> Stmt -> Stmt -> Stmt
| For : Stmt -> BExp -> Stmt -> Stmt ->Stmt
| forcontent : BExp -> Stmt -> Stmt -> Stmt
| get_func : string -> list string -> Stmt
| break : Stmt
| continue  : Stmt
| switch: AExp -> list cases -> Stmt
| read: string -> Stmt
| write: STREXP -> Stmt
| strcpy : string -> string -> Stmt
| nullstmt : Stmt
with cases:=
| def: Stmt -> cases
| case : nat -> Stmt -> cases.


Inductive Val :=
| undecl: Val
| unassign: Val
| default: Val
| number: NatType -> Val
| integer : IntType -> Val
| bol: BoolType -> Val
| str: StringType -> Val
| vector: vect -> Val
| code: (list string) -> Stmt -> Val.
Coercion number: NatType >-> Val.
Coercion integer: IntType >-> Val.
Coercion bol: BoolType >-> Val.
Coercion str : StringType >-> Val.


Definition abs_nat (z:Z) : nat :=
  match z with
    | 0 => 0%nat
    | Zpos p => Pos.to_nat p
    | Zneg p => Pos.to_nat p
  end.
Fixpoint list_ascii_to_list_nat (l:list ascii):list nat:=
match l with
| nil =>  nil
| x::l' => (Nat.sub (nat_of_ascii x) 48)::list_ascii_to_list_nat l'
end.

Fixpoint list_int_to_list_nat (l:list IntType): list nat :=
match l with
| nil => nil
| x::l' => match x with
          |error_int => abs_nat 0::list_int_to_list_nat l'
          |nr x'=> (abs_nat x')::list_int_to_list_nat l'
          end
end.

Fixpoint list_NatType_to_list_nat (l:list NatType): list nat :=
match l with
| nil => nil
| x::l' => match x with
          |error_nat => (abs_nat 0)::list_NatType_to_list_nat l'
          |num x'=> (x')::list_NatType_to_list_nat l'
          end
end.
Fixpoint list_nat_to_list_int (l:list nat):list Z:=
match l with
| nil => nil
| x::l' =>  (Z_of_nat x)::list_nat_to_list_int l'
end.
Fixpoint list_Z_to_list_IntType (l:list Z): list IntType:=
match l with
| nil => nil
| x::l' =>  nr x::  list_Z_to_list_IntType l'
end.
Fixpoint list_BoolType_to_list_nat (l:list BoolType): list nat :=
match l with
| nil => nil
| x::l' => match x with
          |error_bool => (abs_nat 0)::list_BoolType_to_list_nat l'
          |boolean x'=> match(x')with
                        |false => (abs_nat 0)::list_BoolType_to_list_nat l'
                        |true => (abs_nat 1)::list_BoolType_to_list_nat l'
                        end
          end
end.
Fixpoint list_StrType_to_list_nat (l:list StringType): list nat :=
match l with
| nil => nil
| x::l' => match x with
          |error_string => (abs_nat 0)::list_StrType_to_list_nat l'
          |strval x'=> list_sum(list_ascii_to_list_nat(list_ascii_of_string(x')))::list_StrType_to_list_nat l'
          end
end.
Definition natural (val : Val) : nat :=
match val with
| undecl=> 0
| unassign=> 0
| default=> 0
| number n=> (match n with 
            |error_nat => 0
            |num n' => n' 
            end )
| integer i=> (match i with 
               | error_int =>0
               | nr i' =>  ( abs_nat i' )end)
| bol b=> (match b with 
          | error_bool => 0
          | boolean b' => match b' with
                          | true => 1
                          | false => 0 end
          end)  
| str s=> match s with
          | error_string => 0
          | strval s' => list_sum(list_ascii_to_list_nat(list_ascii_of_string(s'))) end
| vector v=>  match v with
              |error_vect => 0
              | vector_int n i'=> list_sum(list_int_to_list_nat(i')) 
              | vector_nat n n'=> list_sum(list_NatType_to_list_nat(n'))
              | vector_bool n b'=> list_sum(list_BoolType_to_list_nat(b'))
              | vector_str n s'=> list_sum(list_StrType_to_list_nat(s'))
              end
| code l s => 1
end.

Definition integ (val : Val) : Z :=
match val with
| undecl=> 0
| unassign=> 0
| default=> 0
| number n=> match n with
            | error_nat => 0
            | num n' => Z_of_nat n'
            end
| integer i=> match i with
              | error_int => 0
              | nr i' => i'
              end
| bol b=> match b with
          | error_bool => 0
          | boolean b' => match b' with
                          | true => 1
                          | false => 0
                          end
          end
| str s=> match s with
          | error_string => 0
          | strval s' => Z_of_nat (list_sum(list_ascii_to_list_nat(list_ascii_of_string(s'))))
          end
| vector v=>  match v with
              |error_vect => 0
              | vector_int n i'=> Z_of_nat (list_sum(list_int_to_list_nat(i'))) 
              | vector_nat n n'=> Z_of_nat (list_sum(list_NatType_to_list_nat(n')))
              | vector_bool n b'=> Z_of_nat (list_sum(list_BoolType_to_list_nat(b')))
              | vector_str n s'=> Z_of_nat (list_sum(list_StrType_to_list_nat(s')))
              end
| code l s => 1
end.

Definition boole (val : Val) : bool :=
match val with
| undecl=> false
| unassign=> false
| default=> false
| number n=> match n with
            | error_nat => false
            | num n' => if(Nat.eqb n' 0) then false else true
            end
| integer i=> match i with 
            | error_int => false
            | nr i' =>  if(Z.leb i' 0 ) then false else true
            end
| bol b=> match b with
          | error_bool => false
          | boolean b' => b'
          end
| str s=> match s with
          |error_string => false
          | strval s' => if(string_dec s' "") then false else true
          end
| vector v=> match v with
              |error_vect => false
              | vector_int n i'=> true
              | vector_nat n n'=> true
              | vector_bool n b'=> true
              | vector_str n s'=> true
              end 
| code l s => true
end.


Definition strng (val : Val) : string :=
match val with
| undecl=> ""
| unassign=> ""
| default=> ""
| number n=> match n with
             | error_nat => ""
             | num n' => string_of_list_ascii(cons (ascii_of_nat n') nil)
             end
| integer i=> match i with 
              | error_int => "" 
              | nr i' => string_of_list_ascii(cons (ascii_of_nat(abs_nat i')) nil)
              end
| bol b=> match b with
          | error_bool => ""
          | boolean b' => match  b' with
                          | true => "true"
                          | false => "false"
                          end
          end
| str s=> match s with
          | error_string => ""
          | strval s' => s'
          end
| vector v=>  match v with
              | error_vect => ""
              | vector_int n i'=> match i' with
                                  | nil => ""
                                  | x::l => "x"
                                  end
              | vector_nat n n'=> match n' with
                                  | nil => ""
                                  | x::l => "x"
                                  end
              | vector_bool n b'=> match b' with
                                  | nil => ""
                                  | x::l => "x"
                                  end
              | vector_str n s'=> match s' with
                                  | nil => ""
                                  | x::l => match x with
                                            |error_string => ""
                                            | strval s' => s'
                                            end
                                  end
              end
| code l s => "code"
end.
Definition vect_list_s (val :Val) :list StringType:=
match val with
| undecl=> error_string::nil
| unassign=> error_string::nil
| default=> error_string::nil
| number n=> error_string::nil
| integer i=> error_string::nil
| bol b=> error_string::nil
| str s=> error_string::nil
| vector v=>  match v with
              | error_vect => error_string::nil
              | vector_int n i'=> error_string::nil
              | vector_nat n n'=> error_string::nil
              | vector_bool n b'=> error_string::nil
              | vector_str n s'=> match s' with
                                  | nil => nil
                                  | x::l => x::l
                                  end
              end
| code l s => error_string::nil
end
.
Definition vect_list_a (val :Val) :list IntType:=
match val with
| undecl=> error_int::nil
| unassign=> error_int::nil
| default=> error_int::nil
| number n=> error_int::nil
| integer i=> error_int::nil
| bol b=> error_int::nil
| str s=> error_int::nil
| vector v=>  match v with
              | error_vect => error_int::nil
              | vector_int n i'=> match i' with
                                  | nil => nil
                                  | x::l => x::l
                                  end
              | vector_nat n n'=> match n' with
                                  | nil => nil
                                  | x::l => match x with
                                            | error_nat => nr 0::list_Z_to_list_IntType(list_nat_to_list_int(list_NatType_to_list_nat l))
                                            | num p=> (nr (Z_of_nat p))::list_Z_to_list_IntType(list_nat_to_list_int(list_NatType_to_list_nat l))
                                            end
                                  end
              | vector_bool n b'=> error_int::nil
              | vector_str n s'=>  error_int::nil
              end
| code l s =>error_int::nil
end.
Definition vect_list_b (val :Val) :list BoolType:=
match val with
| undecl=> error_bool::nil
| unassign=> error_bool::nil
| default=> error_bool::nil
| number n=> error_bool::nil
| integer i=> error_bool::nil
| bol b=> error_bool::nil
| str s=> error_bool::nil
| vector v=>  match v with
              | error_vect => error_bool::nil
              | vector_int n i'=> error_bool::nil
              | vector_nat n n'=> error_bool::nil
              | vector_bool n b'=> match b' with
                                  | nil => nil
                                  | x::l => x::l
                                  end
              | vector_str n s'=>  error_bool::nil
              end
| code l s => error_bool::nil
end
.
Definition Env := string -> Val.
Inductive Envs := 
|pair: Env -> Env -> Envs.
Definition env_loc : Env := fun x => undecl.
Definition env_globe : Env := fun x => undecl.
Definition newenvs (e:Envs): Envs:= 
match e with
| pair e1 e2 => pair env_globe env_loc
end.
Definition envs0 := pair env_loc env_globe. 
Definition is_undecl (val:Val) :=
match val with
| undecl =>true
| _ => false
end.
Definition isglb(e:Envs)(s:string):bool:=
match e with
|pair e1 e2 => if(is_undecl(e2 s)) then true else false
end.
Definition gl(e:Envs)(s:string):Env:=
match e with
|pair e1 e2 => if(isglb e s) then e1 else e2
end.

Definition streval (str:STREXP) (env:Envs):string:=
match str with
| svar s => strng ((gl env s) s)
| sconst s => match s with
              | error_string => ""
              | strval s' => s'
              end
| get_vval_s s n => vect_s_parse n (vect_list_s((gl env s) s)) string("")
| strcat s1 s2 => ( s1 ++ s2)
| to_string s => strng(( gl env s) s)
end.


Definition eq_vals (val1:Val) (val2:Val) :=
match val1 with
| undecl =>  match val2 with
              | undecl => true
              | _ => false
              end
| unassign =>match val2 with
              | unassign => true
              | _ => false
              end
| default=>match val2 with
              | default => true
              | _ => false
              end
| number n=>match val2 with
              | number n'=> true
              | _ => false
              end
| integer i=>match val2 with
              | integer i'=> true
              | _ => false
              end
| bol b=>match val2 with
              | bol b'=> true
              | _ => false
              end
| str s=>match val2 with
              | str s'=> true
              | _ => false
              end
| vector v=>match val2 with
              | vector v'=> true
              | _ => false
              end
| code l c=>match val2 with
              | code l' c'=> true
              | _ => false
              end
end.
Definition update (env : Env) (str : string) (val : Val): Env :=
  fun str' => if (string_dec str str') then val else env str'.
Definition update_env (env:Env) (env1:Env): Env:=
  fun str => if( is_undecl(env1 str) ) then env str else (update env str (env1 str)) str
.
Definition update_envs (e:Envs)(s: string)(v:Val):Envs:=
match e with
| pair g l=>  if(isglb e s) then pair (update g s v) l else pair g (update l s v)
end.

Fixpoint list_update (env : Env) (l:list string) (env1 : Env) :=
  match l with
  |c::l' => list_update (update env c (env1 c)) l' env1
  |nil => env
  end
.
Definition update_local (e:Envs)(s: string)(v:Val):Envs:=
match e with
| pair g l=> pair g (update l s v)
end.
Definition update_global (e:Envs)(s: string)(v:Val):Envs:=
match e with
| pair g l=> pair (update g s v) l 
end.
Definition get_globe(e:Envs):Env:=
match e with
| pair g l=> g
end.
Definition get_local(e:Envs):Env:=
match e with
| pair g l=> l
end.
Definition update_env_g (e1 e2:Envs):Envs:=
match e1 with
| pair g l=> match e2 with
             |pair g' l' => pair (update_env g g') l
             end
end.
Fixpoint lists_parse (l: list string) (l1 : list string) (env:Envs) (env1: Envs):Envs:=
  match l,l1 with
  | nil, nil => pair (get_globe env) (get_local env1)
  | x::l', x1::l1' => if(negb (isglb env x1)) then lists_parse l' l1' env (update_local env1 x ( (get_local env) x1)) else lists_parse l' l1' env env1
  | _, _ => envs0 
  end
.
Fixpoint lists_parse_i (l: list string) (l1 : list string) (env:Envs) (env1: Envs):Envs:=
  match l,l1 with
  | nil, nil => env1
  | x::l', x1::l1' => lists_parse_i l' l1' env (update_envs env1 x ((gl env x1) x1)) 
  | _, _ => envs0 
  end
.
Compute env_loc "x".
Inductive Lang := 
| funcMain : Stmt -> Lang
| funcs : string -> list string -> Stmt -> Lang
| gdecl_int : string -> AExp -> Lang
| gdecl_nat : string -> AExp -> Lang
| gdecl_str : string -> STREXP -> Lang
| gdecl_bool : string -> BExp -> Lang
| gdecl_int0 : string -> Lang
| gdecl_nat0 : string -> Lang
| gdecl_str0 : string -> Lang
| gdecl_bool0 : string -> Lang
| secv : Lang -> Lang-> Lang
.

Fixpoint vect_parse {A:Type}(n:nat)(l:list A)(def: A): A:=
match n, l with 
| O,  x::l' => x
| O, other => def
| S m, nil => def
| S m,  x::l' => vect_parse m l' def
end.
Fixpoint concat (s1 s2 : string) : string :=
  match s1 with
  | EmptyString => s2
  | String c s1' => String c (concat s1' s2)
  end
.

Definition plus_ErrorInt (n1 n2 : IntType) : IntType :=
  match n1, n2 with
    | error_int, _ => error_int
    | _, error_int => error_int
    | nr v1, nr v2 => nr (v1 + v2)
    end.

Definition sub_ErrorInt (n1 n2 : IntType) : IntType :=
  match n1, n2 with
    | error_int, _ => error_int
    | _, error_int => error_int
    | nr n1, nr n2 => nr (n1 - n2)
    end.

Definition mul_ErrorInt (n1 n2 : IntType) : IntType :=
  match n1, n2 with
    | error_int, _ => error_int
    | _, error_int => error_int
    | nr v1, nr v2 => nr (v1 * v2)
    end.

Definition div_ErrorInt (n1 n2 : IntType) : IntType :=
  match n1, n2 with
    | error_int, _ => error_int
    | _, error_int => error_int
    | _, nr 0 => error_int
    | nr v1, nr v2 => nr (Z.div v1 v2)
    end.

Definition mod_ErrorInt (n1 n2 : IntType) : IntType :=
  match n1, n2 with
    | error_int, _ => error_int
    | _, error_int => error_int
    | _, nr 0 => error_int
    | nr v1, nr v2 => nr (v1 - v2 * (Z.div v1 v2))
    end.
Definition pow_ErrorInt (n1 n2 : IntType) : IntType :=
  match n1, n2 with
    | error_int, _ => error_int
    | _, error_int => error_int
    | nr v1, nr v2 => nr (Z.pow v1 v2)
    end.

Reserved Notation "A -[ S ]-> N" (at level 60).
Inductive seval : STREXP -> Envs -> StringType -> Prop:=
| s_const : forall s sigma, sconst s-[ sigma ]-> s
| s_var : forall s sigma, svar s-[ sigma ]->strval(strng((gl sigma s) s))
| s_cat : forall s1 s2 sigma s12 s1' s2',
  s1'= (streval s1 sigma) ->
  s2'= (streval s2 sigma) ->
  s12 = (concat s1' s2') ->
  strcat s1' s2' -[ sigma ]-> strval s12
| s_get_vval_s : forall s n l sigma v,
  l= vect_list_s ((gl sigma s) s) ->
  v=vect_parse n l error_string ->
  get_vval_s s n -[sigma]->v
| s_to_string:forall s sigma s',
  s' = strng ((gl sigma s) s) ->
  to_string s -[sigma]-> strval s'
where "a -[ sigma ]-> s" := (seval a sigma s).

Reserved Notation "A =[ S ]=> N" (at level 60).

Fixpoint length_str (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String c s' => S (length_str s')
  end.
Definition inttype_to_z (i:IntType):Z:=
match i with
| error_int => 0
| nr i' => i'
end.
Definition NatType_to_nat (n: NatType): nat :=
match n with
         | error_nat => 0
         | num n' => n' 
         end
.

Inductive aeval_int : AExp -> Envs -> IntType-> Prop :=
| const_nat : forall  n sigma, anum n =[ sigma ]=> integ n (* <n,sigma> => <n> *) 
| const_int : forall  n sigma, aint n =[ sigma ]=>  n (* <n,sigma> nat=> <n> *) 
| var : forall v sigma, avar v =[ sigma ]=> ( integ((gl sigma v)v)) (* <v,sigma> => sigma(x) *)
| add : forall a1 a2 i1 i2 v1 v2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    v1 = (integ i1) ->
    v2 = (integ i2) ->
    n = plus_ErrorInt v1 v2 ->
    a1 +' a2 =[sigma]=> n
| times : forall a1 a2 i1 i2 v1 v2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    v1 = (integ i1) ->
    v2 = (integ i2) ->
    n = mul_ErrorInt v1 v2 ->
    a1 *' a2 =[sigma]=> n
| dec: forall a1 a2 i1 i2 v1 v2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    v1 = (integ i1) ->
    v2 = (integ i2) ->
    n =  sub_ErrorInt v1 v2 ->
    a1 -' a2 =[sigma]=> n
| div : forall a1 a2 i1 i2 v1 v2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    v1 =( integ i1) ->
    v2 = (integ i2) ->
    n = ( div_ErrorInt v1 v2) ->
    a1 /' a2 =[sigma]=> n
| modu: forall a1 a2 i1 i2 v1 v2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    v1 = (integ i1) ->
    v2 = (integ i2) ->
    n = (mod_ErrorInt v1 v2) ->
    a1 %' a2 =[sigma]=> n
| pow: forall a1 a2 i1 i2 v1 v2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    v1 = (integ i1) ->
    v2 = (integ i2) ->
    n =( pow_ErrorInt v1 v2) ->
    i1 ^' i2 =[sigma]=>n
| tonat : forall s1 sigma,
    to_nat s1 =[ sigma ]=> (integ((gl sigma s1) s1))
| toint : forall s1 sigma,
    to_int s1 =[ sigma ]=> (integ ((gl sigma s1)s1))
| len: forall s sigma,
    strlen s =[ sigma ]=> integ(length_str s)
| e_getvval_a : forall s n l sigma v,
  l= vect_list_a ((gl sigma s) s) ->
  v=vect_parse n l error_int ->
  get_vval_a s n =[sigma]=>v
where "a =[ sigma ]=> n" := (aeval_int a sigma n).


Reserved Notation "B ={ S }=> B'" (at level 70).

Definition IntType_to_Z (i: IntType) :Z:=
match  i with
|error_int => 0
|nr i' => i'
end.
Definition StringType_to_string (s: StringType) :string:=
match s with
|error_string => ""
|strval s' => s'
end.
Definition stringeq (s1 s2:string) :bool:=
if(string_dec s1 s2) then true else false
.
Inductive beval : BExp -> Envs -> BoolType -> Prop :=
| e_true : forall sigma, btrue ={ sigma }=> true
| e_false : forall sigma, bfalse ={ sigma }=> false
| e_var : forall v sigma, bvar v ={ sigma }=> (boole ((gl sigma v) v))
| e_val : forall v sigma, boolean v ={sigma}=> v
| e_blt : forall a1 a2 i1 i2 v1 v2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    v1 = IntType_to_Z i1->
    v2 = IntType_to_Z i2->
    b = Z.ltb v1 v2 ->
    a1 <' a2 ={ sigma }=> b
| e_nottrue : forall b sigma,
    b ={ sigma }=> true ->
    (bnot b) ={ sigma }=> false
| e_notfalse : forall b sigma,
    b ={ sigma }=> false ->
    (bnot b) ={ sigma }=> true
| e_andtrue : forall b1 b2 sigma t,
    b1 ={ sigma }=> true ->
    b2 ={ sigma }=> t ->
    band b1 b2 ={ sigma }=> t
| e_andfalse : forall b1 b2 sigma,
    b1 ={ sigma }=> false ->
    band b1 b2 ={ sigma }=> false
| e_bgt : forall a1 a2 i1 i2 v1 v2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    v1 = IntType_to_Z i1->
    v2 = IntType_to_Z i2->
    b = Z.ltb v2 v1->
    a1 >' a2 ={ sigma }=> b
| e_ortrue :forall b1 b2 sigma,
    b1 ={ sigma }=> true ->
    bor b1 b2 ={ sigma }=> true
| e_orfalse : forall b1 b2 sigma t,
    b1 ={ sigma }=> false ->
    b2 ={ sigma }=> t ->
    bor b1 b2 ={ sigma }=> t
| e_blet : forall a1 a2 i1 i2 v1 v2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    v1 = IntType_to_Z i1->
    v2 = IntType_to_Z i2->
    b = Z.leb v1 v2 ->
    a1 <=' a2 ={ sigma }=> b
| e_bget : forall a1 a2 i1 i2 v1 v2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    v1 = IntType_to_Z i1->
    v2 = IntType_to_Z i2->
    b = Z.leb v2 v1 ->
    a1 <=' a2 ={ sigma }=> b
| e_xor_true_tf : forall b1 b2 sigma,
    b1 ={ sigma }=> true ->
    b2 ={ sigma }=> false ->
    bxor b1 b2 ={ sigma }=> true 
| e_xor_true_ft : forall b1 b2 sigma,
    b1 ={ sigma }=> false ->
    b2 ={ sigma }=> true ->
    bxor b1 b2 ={ sigma }=> true 
| e_xor_false : forall b1 b2 sigma t,
    b1 ={ sigma }=> t ->
    b2 ={ sigma }=> t ->
    bxor b1 b2 ={ sigma }=> false
| e_xand_true : forall b1 b2 sigma t,
    b1 ={ sigma }=> t ->
    b2 ={ sigma }=> t ->
    bxand b1 b2 ={ sigma }=> true
| e_xand_false_tf : forall b1 b2 sigma,
    b1 ={ sigma }=> true ->
    b2 ={ sigma }=> false ->
    bxand b1 b2 ={ sigma }=> false  
| e_xand_false_ft : forall b1 b2 sigma,
    b1 ={ sigma }=> false ->
    b2 ={ sigma }=> true ->
    bxand b1 b2 ={ sigma }=> false
| e_beq : forall a1 a2 i1 i2 b v1 v2 sigma,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    v1 = IntType_to_Z i1->
    v2 = IntType_to_Z i2->
    b = Z.eqb v1 v2 ->
    a1 ==' a2 ={ sigma }=> b
| e_bneq_true: forall a1 a2 i1 i2 v1 v2 b sigma, 
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    v1 = IntType_to_Z i1->
    v2 = IntType_to_Z i2->
    b = ( orb ( Z.gtb v1 v2) ( Z.ltb v1 v2)) ->
    a1 !=' a2 ={ sigma }=> b
| e_bneq_false : forall a1 a2 t sigma,
    a1 =[ sigma ]=> t ->
    a2 =[ sigma ]=> t ->
    a1 !=' a2 ={sigma}=> false
| e_strcmp : forall s1 s2 s11 s22 sigma s,
    s1 -[ sigma ]-> s11 ->
    s2 -[ sigma ]-> s22 ->
    s = stringeq (StringType_to_string s11) (StringType_to_string s22) ->
    strcmp s1 s2  ={sigma}=> s
| e_tobol : forall v sigma,
    to_bool v ={ sigma }=> (boole (( gl sigma v) v))
| e_getvval_b : forall s n v l sigma,
    l= vect_list_b ((gl sigma s) s) ->
    v= vect_parse n l error_bool ->
    get_vval_b s n ={sigma}=>v
where "B ={ S }=> B'" := (beval B S B').

Definition get_def (l :cases): Stmt :=
match l with
| def d => d
| case n c => nullstmt
end.
Fixpoint list_cases_parse (n:nat) (l: list cases) : Stmt :=
match l with 
| x::l' => match x with 
              |def s => s
              |case n' s => if(Nat.eqb n' n) then s else list_cases_parse n l'
              end
| nil => nullstmt
end.

Reserved Notation "S -{ sigma }->  sigma'" (at level 60).
Check update.

Definition get_stmt (val:Val) :Stmt:=
match val with
| undecl => nullstmt
| unassign => nullstmt
| default => nullstmt
| number n => nullstmt
| integer i => nullstmt
| bol b => nullstmt
| str s => nullstmt
| vector v => nullstmt
| code l s => s
end.

Definition get_list (val : Val) : list string:=
match val with
| undecl => nil
| unassign => nil
| default => nil
| number n => nil
| integer i => nil
| bol b => nil
| str s => nil
| vector v => nil
| code l s => l
end.

Inductive eval : Stmt -> Envs -> Envs -> Prop :=
| e_def_nat: forall a i x sigma sigma',
    i=[sigma]=>x ->
    sigma' = (update_local sigma a x) ->
    (def_nat a i) -{ sigma }-> sigma' 
| e_def_int: forall a i x sigma sigma',
    i=[sigma]=>x ->
    sigma' = (update_local sigma a x) ->
    (def_int a i) -{ sigma }-> sigma'  
| e_def_bool: forall a i x sigma sigma',
    i={sigma}=>x ->
    sigma' = (update_local sigma a x ) ->
    (def_bool a i) -{ sigma }-> sigma'
| e_def_string: forall a i x sigma sigma',
    i-[sigma]->x ->
    sigma' = (update_local sigma a x) ->
    (def_string a i) -{ sigma }-> sigma'
| e_def_nat0: forall a sigma sigma' ,
    sigma' = (update_local sigma a unassign) ->
    (def_nat0 a) -{ sigma }-> sigma' 
| e_def_int0: forall a sigma sigma',
    sigma' = (update_local sigma a unassign) ->
    (def_int0 a) -{ sigma }-> sigma'  
| e_def_bool0: forall a sigma sigma',
    sigma' = (update_local sigma a unassign ) ->
    (def_bool0 a) -{ sigma }-> sigma'
| e_def_string0: forall a sigma sigma',
    sigma' = (update_local sigma a unassign) ->
    (def_string0 a) -{ sigma }-> sigma'
| e_def_vector_n: forall s n l sigma sigma',
    sigma' =(update_local sigma s (vector(vector_nat n l))) ->
    def_vector s (vector_nat n l) -{sigma}->sigma'
| e_def_vector_i: forall s n l sigma sigma',
    sigma' =(update_local sigma s (vector(vector_int n l)))->
    def_vector s (vector_int n l) -{sigma}->sigma'
| e_def_vector_b: forall s n l sigma sigma',
    sigma' =(update_local sigma s (vector(vector_bool n l)))->
    def_vector s (vector_bool n l) -{sigma}->sigma'
| e_def_vector_s: forall s n l sigma sigma',
    sigma' =(update_local sigma s (vector(vector_str n l)))->
    def_vector s (vector_str n l) -{sigma}->sigma'
| e_assignment: forall a i x sigma sigma',
    (negb (is_undecl((gl sigma a) a)))= true ->
    i =[sigma]=> x ->
    sigma' = (update_envs sigma a x) ->
    (assignment a i) -{ sigma }-> sigma'
| e_bassignment: forall a i x sigma sigma',
    (negb (is_undecl(( gl sigma a)a)))= true ->
    i ={sigma}=> x ->
    sigma' = (update_envs sigma a x) ->
    (bassignment a i) -{ sigma }-> sigma'
| e_sassignment: forall a i x sigma sigma',
    (negb (is_undecl((gl sigma a) a)))= true ->
    i -[sigma]-> x ->
    sigma' = (update_envs sigma a x) ->
    (sassignment a i) -{ sigma }-> sigma'
| e_seq : forall s1 s2 sigma sigma' sigma'',
    s1 -{ sigma }-> sigma' ->
    s2 -{ sigma' }-> sigma'' ->
    (sequence s1 s2) -{ sigma }-> sigma''
| e_whilefalse : forall b s sigma,
    b ={ sigma }=> false ->
    while b s -{ sigma }-> sigma
| e_whiletrue : forall b s sigma sigma',
    b ={ sigma }=> true ->
    (sequence s (while b s)) -{ sigma }-> sigma' ->
    while b s -{ sigma }-> sigma'
| e_iffalse1 : forall b s1 sigma,
    b ={ sigma }=> false ->
    ifthen b s1 -{ sigma }-> sigma
| e_iftrue1 : forall b s1 sigma sigma',
    b ={ sigma }=> true ->
    s1 -{ sigma }-> sigma' ->
    ifthen b s1 -{ sigma }-> sigma'
| e_iffalse2 : forall b s1 s2 sigma sigma',
    b ={ sigma }=> false ->
    s2 -{ sigma }-> sigma' ->
    ifthenelse b s1 s2 -{ sigma }-> sigma'
| e_iftrue2 : forall b s1 s2 sigma sigma',
    b ={ sigma }=> true ->
    s1 -{ sigma }-> sigma' ->
    ifthenelse b s1 s2 -{ sigma }-> sigma'
| e_for_false : forall a b st s1 sigma sigma',
    a -{ sigma }-> sigma' ->
    b ={ sigma' }=> false ->
    For a b st s1 -{ sigma }-> sigma'
| e_for_true : forall a b st s1 sigma sigma' sigma'',
    a -{ sigma }-> sigma' ->
    b ={ sigma' }=> true ->
    (sequence s1 (sequence st  (forcontent b st s1))) -{ sigma' }-> sigma'' ->
    For a b st s1 -{ sigma }-> sigma''
| e_forcontent_false : forall b st s1 sigma,
    b ={ sigma}=> false ->
    forcontent b st s1 -{ sigma }-> sigma
| e_forcontent_true : forall b st s1 sigma sigma',
    b ={ sigma }=> true ->
    (sequence s1 (sequence st (forcontent b st s1))) -{ sigma }-> sigma' ->
    forcontent b st s1 -{ sigma }-> sigma'
| e_dowhile_true : forall st b sigma sigma' sigma'',
    st -{ sigma }-> sigma' ->
    while b st -{ sigma' }-> sigma'' ->
    dowhile st b -{ sigma }-> sigma'
| e_dowhile_false : forall st b sigma sigma',
    st -{ sigma }-> sigma' ->
    b ={ sigma' }=> false ->
    dowhile st b -{ sigma }-> sigma'
| e_switch : forall a b sigma n v sigma',
    a =[ sigma ]=> n ->
    v = (list_cases_parse (abs_nat(IntType_to_Z n)) b ) ->
    v -{ sigma }-> sigma' ->
    switch a (b) -{ sigma }-> sigma'
| e_strcpy : forall s1 s2 sigma sigma' s2',
    s2' = (gl sigma s2) s2 ->
    sigma' = (update_envs sigma s1 s2') ->
    strcpy s1 s2 -{ sigma }-> sigma'
| e_getfunc : forall s l1 sigma sigma' st sigma'' sigma''' l sigma'''',
    l = (get_list ((get_globe sigma) s) ) ->
    length l = length l1 ->
    sigma'= (lists_parse_i l l1 sigma (pair (update_env (get_globe envs0) (get_globe sigma)) (get_local envs0))) ->
    st = get_stmt(get_globe sigma s) ->
    st -{ sigma'}-> sigma'' ->
    sigma''' =(update_env_g sigma sigma'') ->
    sigma'''' =(lists_parse_i l1 l sigma'' sigma''') ->
    get_func s l1 -{sigma}-> sigma'''
| e_null_stmt : forall sigma,
    nullstmt -{sigma}-> sigma
where "s -{ sigma }-> sigma'" := (eval s sigma sigma').

Reserved Notation "A =| sigma |=> B"(at level 0).
Inductive Leval : Lang -> Envs -> Envs -> Prop :=
| e_funcMain: forall s sigma sigma' sigma'',
    (is_undecl ((get_globe sigma) "main")) = true ->
    sigma' =(update_global sigma "main" (code nil s)) ->
    s -{sigma'}->sigma'' ->
    (funcMain s) =| sigma |=> sigma''
| e_funcs: forall s l st sigma sigma',
    (is_undecl ((get_globe sigma) "main")) ={sigma}=> true->
    sigma' = (update_global sigma s (code l st)) ->
    (funcs s l st) =|sigma|=>sigma'
| e_gdecl_int: forall s i x sigma sigma',
    i=[sigma]=>x ->
    sigma' = (update_global sigma s x) ->
    (gdecl_int s i) =|sigma|=> sigma'
| e_gdecl_nat:forall s i x sigma sigma',
    i=[sigma]=>x ->
    sigma' = (update_global sigma s x) ->
    (gdecl_nat s i) =|sigma|=> sigma'
| e_gdecl_str:forall s i x sigma sigma',
    i-[sigma]->x ->
    sigma' = (update_global sigma s x) ->
    (gdecl_str s i) =|sigma|=> sigma'
| e_gdecl_bool:forall s i x sigma sigma',
    i={sigma}=>x ->
    sigma' = (update_global sigma s x) ->
    (gdecl_bool s i) =|sigma|=> sigma'
| e_gdecl_int0:forall s sigma sigma',
    sigma' = (update_global sigma s unassign) ->
    (gdecl_int0 s) =|sigma|=> sigma'
| e_gdecl_nat0:forall s sigma sigma',
    sigma' = (update_global sigma s unassign) ->
    (gdecl_nat0 s) =|sigma|=> sigma
| e_gdecl_str0:forall s sigma sigma',
    sigma' = (update_global sigma s unassign) ->
    (gdecl_str0 s) =|sigma|=> sigma
| e_gdecl_bool0:forall s sigma sigma',
    sigma' = (update_global sigma s unassign) ->
    (gdecl_bool0 s) =|sigma|=> sigma
| e_secv:forall s1 s2 sigma sigma' sigma'',
    s1 =|sigma|=> sigma' ->
    s2 =|sigma'|=> sigma'' ->
    (secv s1 s2) =| sigma |=> sigma''
where "s =| sigma |=> sigma'" :=(Leval s sigma sigma').

Notation "X ::= A" := (assignment X A ) (at level 50).
Notation "X :b:= A" := (bassignment X A ) (at level 50).
Notation "X :s:= A" := (sassignment X A ) (at level 50).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 92).
Notation "'If' ( C ) 'then' { A } 'else' { B } 'end''" := (ifthenelse C A B) (at level 59).
Notation "'If' ( C ) 'then' { A } 'end''" := (ifthen C A) (at level 59).
Notation "'while'' ( A ) { B } " := (while A B) (at level 91).
Notation "'do' { A } 'while' ( B )" := (dowhile A B) (at level 91).
Notation "'for' ( A ; B ; C ) { D }" := (For A B C D) (at level 91).
Notation "'nat' A := B" := (def_nat A B)(at level 50).
Notation "'bool' A := B" := (def_bool A B)(at level 50).
Notation "'int' A := B" := (def_int A B)(at level 50).
Notation "'string' A := B" := (def_string A B)(at level 50).
Notation "'nat' A |" := (def_nat0 A )(at level 50).
Notation "'bool' A |" := (def_bool0 A )(at level 50).
Notation "'int' A |" := (def_int0 A )(at level 50).
Notation "'string' A |" := (def_string0 A )(at level 50).
Notation "'nat'' A := B" := (gdecl_nat A B)(at level 50).
Notation "'bool'' A := B" := (gdecl_bool A B)(at level 50).
Notation "'int'' A := B" := (gdecl_int A B)(at level 50).
Notation "'string'' A := B" := (gdecl_str A B)(at level 50).
Notation "'nat'' A |" := (gdecl_nat0 A )(at level 50).
Notation "'bool'' A |" := (gdecl_bool0 A )(at level 50).
Notation "'int'' A |" := (gdecl_int0 A)(at level 50).
Notation "'string'' A |" := (gdecl_str0 A )(at level 50).

Notation "'default' : { A }" := (def A) (at level 92).
Notation "'case' ( A ) : { B }" := (case A B) (at level 92).
Notation "'switch'' ( A ) : { B } " := (switch A (cons B nil)) (at level 93).
Notation "'switch'' ( A ) : { B1 ; B2 ; .. ; Bn }" := (switch A (cons B1 (cons B2 .. (cons Bn nil) ..))) (at level 93).
Notation "'(int)'  A  " := (to_int A)( at level 35).
Notation "'(nat)'  A " := (to_nat A)( at level 35).
Notation "'(bool)'  A " := (to_bool A)( at level 35).
Notation "'(string)'  A " := (to_string A)( at level 35).
Notation "'func'' main():{ C }" := (funcMain C )(at level 97).
Notation "'func'' A (( B1 ; B2 ; .. ; Bn )):{ C }" := (funcs A (cons B1 (cons B2 .. (cons Bn nil) ..)) C )(at level 97).
Notation "'func'' A (( B )):{ C }" := (funcs A (cons B nil) C )(at level 97).
Notation "A ';;'' B" := (secv A B)(at level 96).
Notation "'->' A (( B1 ; B2 ; .. ; Bn )) " := (get_func A (cons B1 (cons B2 .. (cons Bn nil) ..)))(at level 91).
Notation "'int' A [ B ]={ C1 ; C2 ; .. ; Cn }" := ( def_vector A ( vector_int B (cons int(C1) (cons int(C2) .. (cons int(Cn) nil) ..) ) ) )(at level 50).
Notation "'nat' A [ B ]={ C1 ; C2 ; .. ; Cn }" := ( def_vector A ( vector_nat B (cons nat(C1) (cons nat(C2) .. (cons nat(Cn) nil) ..) ) ) )(at level 50).
Notation "'bool' A [ B ]={ C1 ; C2 ; .. ; Cn }" := ( def_vector A ( vector_bool B (cons bool(C1) (cons bool(C2) .. (cons bool(Cn) nil) ..) ) ) )(at level 50).
Notation "'string' A [ B ]={ C1 ; C2 ; .. ; Cn }" := ( def_vector A ( vector_str B (cons string(C1) (cons string(C2) .. (cons string(Cn) nil) ..) ) ) )(at level 50).
Notation "'int' A [ B ]" := ( def_vector A ( vector_int B nil ) )(at level 50).
Notation "'nat' A [ B ]" := ( def_vector A ( vector_nat B nil ) )(at level 50).
Notation "'bool' A [ B ]" := ( def_vector A ( vector_bool B nil ) )(at level 50).
Notation "'string' A [ B ]" := ( def_vector A ( vector_str B nil ) )(at level 50).

Notation "A a[ B ]" :=(get_vval_a A B)(at level 51).
Notation "A s[ B ]" :=(get_vval_s A B)(at level 51).
Notation "A b[ B ]" :=(get_vval_b A B)(at level 51).

Compute switch' (5) : {case (1): {If(1=='1) then {nat "AA" := 7} else {int "BB" := 7} end'} ; case(2): {If(1=='1) then {int "CC":= 13}end'} ; default : {bool "3" := true}}.
Compute int "ASD" [50]={ -1 ; 2 ; -3 }.
Compute nat "ASD"[50]={ 1 ; 2 ; 3 }.
Compute bool "ASD"[50]={ true ; false ; true }.
Compute string "ASD"[50]={ "1" ; "2" ; "3" }.
Compute nat "ASD"[50].
Compute "ASD"a[50].
Compute func' main():{ If( 1=='1) then { "x" ::= 3 } end' }.
Compute func' "test" (( "text1" )):{
           If ( 1 ==' 1 ) then 
              { "text1" :s:= string( "test" ) } end' } .
Compute func' "test" (( "text1" ; "text2" )):{
          If ( 1 ==' 1 ) then 
            { -> "test" (( "text1" ; "text2" )) 
            } end' ;;
            string "QWE"[55]
          } ;;' 
          int' "x" := 5 ;;' 
          func' main():{ 
          If( 1=='1) then 
            { "x" ::= 3 ;; int "y" | ;; int "j" := 7 ;; -> "test" (("x" ; "y"));; string "u" :=(string) "j" }
            end'
          }.


Definition alg1 :=
  func' "test" (("abc"; "bcd"; "aac")):{
    "abc" ::= 3;;
    "bcd" ::= 40 ;;
    "aac" ::= 60 ;;
    "n" ::=55
  } ;;'
  int' "n" := 1 ;;'
  int' "x" := 0 ;;'
  func' main():{
  int "i" := 1 ;;
  int "sum" := 0 ;;
  If ( "i" <=' "n" ) then {
          "sum" ::= "sum" +' "i" ;;
          "i" ::= "i" +' 1
        }
  else {
    "sum" ::= "sum" +' 50 ;;
    "i" ::= "i" +' 15 ;;
    "x" ::= "sum" /' "i" ;;
    string "qeq" := string("abc");;
    string "eqe" := string("ddf");;
    string "aaaa" := strcat("qeq", "eqe")
  }
  end';;
  -> "test" (("n" ; "sum" ; "i"))
}.
Check func' "test" (("abc"; "bcd"; "aac")):{
    "abc" ::= 3;;
    "bcd" :s:= "sss" 
  }. 
Example eval_alg1 :
  exists state,
  alg1 =| envs0 |=> state /\ (gl state "n")"n" = 55.
Proof.
eexists.
split.
  - unfold alg1. eapply e_secv. eapply e_secv. eapply e_secv. 
  + eapply e_funcs; eauto.  simpl. eapply e_val;eauto.
  + eapply e_gdecl_int;eauto. eapply const_int.
  + eapply e_gdecl_int;eauto. eapply const_int.
  + eapply e_funcMain; eauto. simpl. eapply e_seq.
    ++ eapply e_seq. eapply e_seq.
      eapply e_def_int; eauto. eapply const_int.
      eapply e_def_int; eauto. eapply const_int.
      eapply e_iftrue2.
        +++ eapply e_blet; eauto.
            ++++ eapply var.
            ++++ eapply var.
            ++++ trivial. 
        +++ eapply e_seq. 
            ++++ eapply e_assignment; eauto. simpl. eapply add; eauto. eapply var. eapply var; eauto. 
            ++++ eapply e_assignment; eauto.
               +++++ simpl. eapply add. eapply var; eauto.  eapply const_int; eauto. trivial. trivial. simpl. trivial.
    ++ eapply e_getfunc; eauto. simpl. eapply e_seq; eauto. eapply e_seq; eauto. 
    eapply e_seq. eapply e_assignment; eauto. simpl. eapply const_int. eapply e_assignment; 
    eauto. simpl. eapply const_int. eapply e_assignment; eauto. simpl. eapply const_int. 
    eapply e_assignment; eauto. eapply const_int. 
-  simpl. unfold update_env. simpl. unfold update. simpl. reflexivity.
Qed. 
Definition alg2 :=

func' main():{
int "y"[50]={1 ;2 ;3} ;;
int "a" := ("y"a[0]) ;;
switch' ("a"):{
    case (1):{
       If(1=='1) then {nat "AA" := 7} 
        else {int "BB" := 7} end'
    } ;
    case(2): {
       If(1=='1) then {int "CC":= 13}end'
    } ;
    default : {bool "3" := true}
  };;
  bool "ghi" := (bool)"a" ;;
  do {
  "a"::="a" +' 1
  } while("a"<' 2) ;;
  "ghi" :b:= ("ghi" xor' true)
}.
Example eval_alg2 :
  exists state,
  alg2 =| envs0 |=> state /\ (gl state "AA")"AA" = 7 /\ (gl state "ghi")"ghi" = false.
Proof.
eexists.
split.
unfold alg2.
- eapply e_funcMain; eauto. eapply e_seq. eapply e_seq. eapply e_def_vector_i; eauto.
eapply e_def_int; eauto. eapply e_getvval_a; eauto. eapply e_seq. eapply e_seq. 
eapply e_seq. eapply e_switch; eauto. eapply var. unfold list_cases_parse. simpl.
eapply e_iftrue2. eapply e_beq;eauto. eapply const_int. eapply const_int.
trivial. eapply e_def_nat;eauto. eapply const_int. eapply e_def_bool;eauto. eapply e_tobol.
eapply e_dowhile_false;eauto. eapply e_assignment;eauto. simpl. eapply add;eauto. eapply var. eapply const_int.
eapply e_blt;eauto. eapply var. eapply const_int. simpl. trivial. eapply e_bassignment;eauto.
eapply e_xor_false; eauto. eapply e_var. simpl.  eapply e_val.
- simpl. unfold update. simpl. split. trivial. trivial.
Qed.




