namespace Kanren

module Stream =
    open System.Collections
    open System.Collections.Generic
    type Stream<'a> = 
    | Nil
    | Cons of 'a * Stream<'a>
    | Thunk of Lazy<Stream<'a>>
        member this.toSeq () =
            match this with
            | Nil -> Seq.empty
            | Cons (x,xs) -> seq { x; yield! xs}
            | Thunk t -> seq { yield! t.Force().toSeq() }
        interface IEnumerable with
            member this.GetEnumerator() =
                this.toSeq().GetEnumerator()
            
        interface IEnumerable<'a> with
            member this.GetEnumerator() =
                this.toSeq().GetEnumerator()
    let just x = Cons (x,Nil)
    let rec mplus m1 m2 = 
        match m1 with
        | Nil -> m2
        | Cons (x,xs) -> Cons (x, mplus m2 xs)
        | Thunk t -> Thunk (lazy (mplus m2 (t.Force())))
    let rec bind m f =
        match m with
        | Nil -> Nil
        | Cons(x,xs) -> mplus (f x) (bind xs f)
        | Thunk t -> Thunk (lazy (bind (t.Force()) f))

module Logic =
    open Stream
    open FSharpPlus
    open FSharpPlus.Data
    open FSharp.Quotations
    open FSharp.Quotations.Evaluator

    type Term<'a> =
    | Var of int
    | Value of 'a
    | Pair of Term<'a> * Term<'a>
    | Empty

    type Subst<'a> = Subst of Map<int, Term<'a>> * int

    type Goal<'a> = State<Subst<'a>,Stream<Subst<'a>>>  

    let fresh () : State<Subst<'a>,Term<'a>> =
        monad {
            let! Subst (s,x)= get
            do! put (Subst (s,x+1))
            return (Var x)
        }
    let rec walk v m =
        match v with
        | Value a -> Value a
        | Empty -> Empty
        | Pair (a,b) -> Pair (walk a m, walk b m)
        | Var i ->
            match Map.tryFind i m with
            | Some v' -> walk v' m
            | None -> Var i
    let conj m (n: Goal<'a>) : Goal<'a> =
        monad {
            let! (x: Stream<Subst<'a>>) = m
            Stream.bind x (fun s -> State.eval n s)
        }
    let rec unify (u: Term<'a>) (v:Term<'a>) :  Goal<'a> =
        monad {
            let! Subst (m, c) = get
            match walk u m, walk v m with
            | Value a, Value b -> 
                if a = b then 
                    just (Subst (m,c))
                else
                    Stream.Nil
            | Var a, Var b ->
                if a = b then 
                    just (Subst (m,c))
                else
                    Stream.Nil
            | a, Var i
            | Var i, a ->
                just (Subst (Map.add i a m, c))
            | Empty, Empty -> just (Subst (m,c))
            | Pair(a1,b1), Pair(a2,b2) -> 
                return! conj (unify a1 a2) (unify b1 b2)
            | _ -> Stream.Nil
        }
    let eq u v = unify u (Value v)
    let disj m n : Goal<'a> =
        monad {
            let! (x:Stream<Subst<'a>>) = m
            let! (y: Stream<Subst<'a>>) = n
            mplus x y
        }
    
    let disjP exprs =
        exprs |> Seq.reduce disj
    let conjP exprs =
        exprs |> Seq.reduce conj
    let conde branches =
        branches
        |> Seq.map conjP
        |> disjP

    let neq u v =
        monad {
            let! matches = unify u v
            let! s = get
            if matches |> Seq.length > 0 then
                return Stream.Nil
            else
                return just s
        }
    let run l = State.eval l (Subst (Map.empty, 0))

    let delay (x: Expr<Goal<'a>>) =
        QuotationEvaluator.Evaluate <@ (State (fun s -> Thunk (lazy (State.eval (%x) s)), s)) @>

