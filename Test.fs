module Test
open Kanren.Logic
open FSharpPlus
open FSharpPlus.Data
open Xunit
open Xunit.Abstractions
let parents p c: Goal<string> =
    conde [
        [eq p "Allan"; eq c "Sarah"]
        [eq p "Alice"; eq c "Sarah"]
        [eq p "Allan"; eq c "Steve"]
        [eq p "Alice"; eq c "Steve"]
    ]

let feels (a:Term<string>) =
    disjP [
    unify a <| Pair (Value "Alice", Pair (Value "likes", Value "Bob")) 
    unify a <| Pair (Value "Alice", Pair (Value "hates", Value "John")) 
    ]
let rec fives x: Goal<int> =
    disj (eq x 5) (delay <@fives x@>)
let relo f a1 a2 =
    disj (f a1 a2) (f a2 a1)
let friends p1 p2 =
    let data v1 v2=
        conde [
            [eq v1 "Alice"; eq v2 "Bob"]
            [eq v1 "Alice"; eq v2 "Charlie"]
            [eq v1 "Bob"; eq v2 "Charlie"]
            [eq v1 "David"; eq v2 "Alice"]
            [eq v1 "Ed"; eq v2 "David"]
        ]
            
    relo data p1 p2

let meta p1 p2: Goal<string> =
    monad {
        let! f = fresh ()
        return! conj (friends f p2) (friends f p1)
    }
type KanrenTests (output: ITestOutputHelper) =
    [<Fact>]
    let ``Allan's spouse``  () =
        run (monad {
            let! p = fresh ()
            let! c = fresh ()
            return! conjP [
                (parents (Value "Allan") c) 
                (parents p c)
                neq p (Value "Allan")
            ]
        })
        |> Seq.iter (output.WriteLine << sprintf "%A\n")
    [<Fact>]
    let ``Bob's friends' friends``() =
        run (
            monad {
                let! f = fresh ()
                return! meta f (Value "Bob")
            }
        ) 
        |> Seq.iter (output.WriteLine << sprintf "%A\n")
    [<Fact>]
    let ``five 5s`` () =
        let answer = 
            run (
                monad {
                    let! x = fresh ()
                    return! fives x
                }
            )
            |> Seq.take 5
        Assert.Equal(5, answer |> Seq.length)
        answer
        |> Seq.iter (output.WriteLine << sprintf "%A\n")
    [<Fact>]
    let ``Relationships`` () =
        let answer =
            run (
                monad {
                    let! x = fresh ()
                    let! y = fresh ()
                    return! conj (unify x (Pair (Value "Alice", Pair (Value "likes", y)))) (feels x)
                }
            )
        answer
        |> (output.WriteLine << sprintf "%A\n")