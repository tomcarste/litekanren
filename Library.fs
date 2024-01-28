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
        | Value a -> Choice1Of2 a
        | Var i ->
            match Map.tryFind i m with
            | Some v' -> walk v' m
            | None -> Choice2Of2 i

    let unify (u: Term<'a>) (v:Term<'a>) :  Goal<'a> =
        monad {
            let! Subst (m, c) = get
            match walk u m, walk v m with
            | Choice1Of2 a, Choice1Of2 b -> 
                if a = b then 
                    Cons(Subst (m,c),Stream.Nil)
                else
                    Stream.Nil
            | Choice2Of2 a, Choice2Of2 b ->
                if a = b then 
                    Cons(Subst (m,c),Stream.Nil)
                else
                    Stream.Nil
            | Choice1Of2 x, Choice2Of2 i
            | Choice2Of2 i, Choice1Of2 x ->
                Cons(Subst (Map.add i (Value x) m, c),Stream.Nil)
        }
    let eq u v = unify u (Value v)
    let disj m n : Goal<'a> =
        monad {
            let! (x:Stream<Subst<'a>>) = m
            let! (y: Stream<Subst<'a>>) = n
            mplus x y
        }
    let conj m (n: Goal<'a>) : Goal<'a> =
        monad {
            let! (x: Stream<Subst<'a>>) = m
            Stream.bind x (fun s -> State.eval n s)
        }
    let disjP exprs =
        exprs |> Seq.reduce disj
    let conjP exprs =
        exprs |> Seq.reduce conj
    let conde branches =
        branches
        |> Seq.map conjP
        |> disjP

    let filter u v =
        monad {
            let! matches = unify u v
            let! s = get
            if matches |> Seq.length > 0 then
                return Stream.Nil
            else
                return Cons(s,Stream.Nil)
        }
    let run l = State.eval l (Subst (Map.empty, 0))

    let delay (x: Expr<Goal<'a>>) =
        QuotationEvaluator.Evaluate <@ (State (fun s -> Thunk (lazy (State.eval (%x) s)), s)) @>

