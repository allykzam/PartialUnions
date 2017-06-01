namespace PartialUnions

/// Internal helper type used for tracking arguments and parameters while
/// processing code quotations.
type private ArgumentState =
    /// Holds the value of an argument passed to a function.
    | AppliedValue of value : System.IComparable
    /// Tracks the name of a parameter that a function expects.
    | LambdaParam of name : string
    /// Tracks the parameter name that a function used to supply a value to a
    /// union case constructor, the union case field name to which this
    /// parameter is applied, and the parameter's index in the union case
    /// constructor.
    | UnionParam of localName : string * fieldName : string * paramIndex : int
    /// Holds a literal value supplied to a union case constructor -- typically
    /// indicating a default value pre-applied by a wrapper function -- as well
    /// as the union case field name to which this value is applied, and the
    /// parameter's index in the union case constructor.
    | UnionArg of value : System.IComparable * fieldName : string * paramIndex : int


open Microsoft.FSharp.Quotations
open Microsoft.FSharp.Quotations.Patterns

/// <summary>
/// Contains metadata about a union case, including information about which
/// union case constructor parameters are omitted.
/// </summary>
/// <typeparam name="'T">
/// The discriminated union type for which this metadata is to be stored.
/// </typeparam>
/// <remarks>
/// While the type parameter <typeparamref name="'T" /> is not strictly
/// necessary for any of the fields contained in this type, accurately supplying
/// the type parameter ensures type safety in consuming code which performs
/// comparisons between values.
/// </remarks>
type UnionMetadata<'T when 'T : comparison> =
    {
        /// The name of the union case which this metadata is associated with.
        UnionCase : string;
        /// The union case constructor arguments (or lack thereof) supplied for
        /// this metadata.
        SuppliedArguments : (System.IComparable option * string) list;
    }


    /// <summary>
    /// Indicates whether or not the given reflection data matches the metadata
    /// specification documented in this <see cref="UnionMetadata<'T>" /> value.
    /// </summary>
    /// <param name="unionCase">
    /// The reflected union case information to process.
    /// </param>
    /// <param name="args">
    /// The field values contained in the union value to process.
    /// </param>
    /// <exception cref="System.ArgumentException>
    /// Raised when the given union information is not for the target type
    /// <typeparamref name="'T" />.
    /// </exception>
    /// <remarks>
    /// Since reflection typically has a high performance cost, this function is
    /// available for scenarios where a union value is to be repeatedly compared
    /// against many <see cref="UnionMetadata<'T>" /> values. The given union
    /// value can be reflected upon once, simply passing the values to this
    /// function multiple times.
    /// </remarks>
    member this.UnionInfoMatches (unionCase : Reflection.UnionCaseInfo, args : obj array) : bool =
        // If the union info is not for a value of type 'T, throw an exception.
        if unionCase.DeclaringType <> typeof<'T> then
            sprintf "The given union information must be from a value of type %A"
                typeof<'T>.FullName
            |> invalidArg "unionCase"
        // If given a different union case, then it does not match this
        // metadata.
        if unionCase.Name <> this.UnionCase then false else
        // If the wrong number of arguments exist, assume that the value does
        // not match. This should not happen when valid input is provided based
        // on a value of type 'T.
        if args.Length <> this.SuppliedArguments.Length then false else

        let argMatches (((x : System.IComparable option), _), (y : obj)) =
            match x, y with
            // If this field was omitted in the metadata, any value matches.
            | None, _ -> true
            // If this field was specified as null, null values match.
            | Some null, null -> true
            // If this field was specified as null, and the value is not null,
            // no match.
            | Some null, _ -> false
            // Vice-versa, no match.
            | Some _, null -> false
            // If both the specified value and the actual value are non-null,
            // ask the specified value if it believes itself equal to the actual
            // value.
            | Some x, y -> x.Equals y

        // Zip the value's actual arguments with the metadata specification, and
        // find out if any values do NOT match their specification.
        args
        |> Seq.zip this.SuppliedArguments
        |> Seq.filter (argMatches >> not)
        |> Seq.tryHead
        |> function
           // If no arguments were mismatched, then the entire value matches the
           // specification.
           | None -> true
           // But if ANY arguments did NOT match their specification, then the
           // entire value does not match.
           | Some _ -> false

    /// <summary>
    /// Indicates whether or not the given value matches the metadata
    /// specification documented in this <see cref="UnionMetadata<'T>" /> value.
    /// </summary>
    /// <param name="x">
    /// The value to compare against this value's metadata specification.
    /// </param>
    member this.ValueMatches (x : 'T) : bool = this.UnionInfoMatches (FSharp.Reflection.FSharpValue.GetUnionFields(x, typeof<'T>))

    /// <summary>
    /// Indicates whether or not the given value matches the metadata
    /// specification contained in <paramref name="spec" />.
    /// </summary>
    /// <param name="x">
    /// The union value to process.
    /// </param>
    /// <param name="spec">
    /// The metadata specification to compare <paramref name="x" /> to.
    /// </param>
    static member ValueMatchesSpec (x : 'T) (spec : UnionMetadata<'T>) : bool = spec.ValueMatches x
    /// <summary>
    /// Indicates whether or not the given reflection data matches the metadata
    /// specification contained in <paramref name="spec" />.
    /// </summary>
    /// <param name="x">
    /// The reflected union case information and field values for the union
    /// value to process.
    /// </param>
    /// <param name="spec">
    /// The metadata specification to compare <paramref name="x" /> to.
    /// </param>
    /// <remarks>
    /// Since reflection typically has a high performance cost, this function is
    /// available for scenarios where a union value is to be repeatedly compared
    /// against many <see cref="UnionMetadata<'T>" /> values. The given union
    /// value can be reflected upon once, simply passing the values to this
    /// function multiple times.
    /// </remarks>
    static member UnionInfoMatchesSpec (x : Reflection.UnionCaseInfo * obj array) (spec : UnionMetadata<'T>) : bool = spec.UnionInfoMatches x


    /// <summary>
    /// Takes an <see cref="Expr" /> value, and if possible, creates and returns
    /// a <see cref="ComparableObj" /> instance containing the value.
    /// </summary>
    /// <param name="arg">
    /// An <see cref="Expr" /> value which represents a literal value.
    /// </param>
    static member private UsefulUnionArg (arg : Expr) : System.IComparable option =
        match arg with
        | Var x -> None
        | Value (x, _) ->
            match x with
            | :? System.IComparable as x -> Some x
            | _ -> failwithf "Literal value %A does not implement System.IComparable" x
        | NewUnionCase (x, xs) ->
            xs
            |> Seq.choose UnionMetadata<_>.UsefulUnionArg
            |> Seq.map box
            |> Seq.toArray
            |> fun args -> Some (FSharp.Reflection.FSharpValue.MakeUnion(x, args) :?> System.IComparable)
        | _ -> failwithf "Cannot convert the given value %A into a literal object." arg

    /// <summary>
    /// Decomposes the given <see cref="Expr" /> value into the union case which
    /// the quotation represents, and the arguments provided to it. Note that
    /// the resulting collection of arguments will contain duplicates, and must
    /// be processed to consolidate the values therein.
    /// </summary>
    /// <param name="e">
    /// The <see cref="Expr" /> value to process.
    /// </param>
    static member private ExprToUnionInfo (e : Expr) : Reflection.UnionCaseInfo * (ArgumentState list) =
        // This method operates by recursively calling itself on smaller pieces
        // of the given Expr object until literal values are processed. In the
        // scope of this function, a `Lambda` indicates a parameter that can be
        // supplied, `Application` indicates an argument being supplied for one
        // of the parameters, and `NewUnionCase` is the combination of all
        // potential values and literal values into a new union case.
        match e with
        // Handle function application
        | Application (xs, arg) ->
            let arg = UnionMetadata<_>.UsefulUnionArg arg
            let (unionCase, args) = UnionMetadata<_>.ExprToUnionInfo xs
            unionCase, (AppliedValue (arg.Value))::args

        // Handle lambda parameters
        | Lambda (arg, xs) ->
            let (unionCase, args) = UnionMetadata<_>.ExprToUnionInfo xs
            unionCase, (LambdaParam arg.Name)::args

        // Handle union case construction
        | NewUnionCase (unionCase, args) ->
            let args =
                args
                |> Seq.zip (unionCase.GetFields())
                |> Seq.mapi
                    (fun i (field, arg) ->
                        match arg with
                        | Var x -> UnionParam(x.Name, field.Name, i)
                        | Value _ | NewUnionCase _ ->
                            let x = UnionMetadata<_>.UsefulUnionArg arg
                            UnionArg (x.Value, field.Name, i)
                        | _ -> failwithf "Cannot convert the given value %A into a union argument." arg
                    )
                |> Seq.toList
            unionCase, args

        | _ -> failwithf "Cannot process the given quotation: %A" e


    /// <summary>
    /// Processes the union case constructor arguments and the union case
    /// metadata into a new <see cref="UnionMetadata<'T>" /> value.
    /// </summary>
    /// <param name="unionCase">
    /// The reflection metadata for the target union case.
    /// </param>
    /// <param name="args">
    /// A list of arguments, parameters, etc., which are to be processed.
    /// </param>
    static member private UnionInfoToMetadata ((unionCase : Reflection.UnionCaseInfo), (args : ArgumentState list)) : UnionMetadata<'T> =
        // Find the original argument information, and sort by field order.
        let actualArgs =
            args
            |> Seq.choose
                (fun x ->
                    match x with
                    | UnionParam (v, f, i) -> Some ((Choice1Of2 v), f, i)
                    | UnionArg   (v, f, i) -> Some ((Choice2Of2 v), f, i)
                    | _ -> None
                )
            |> Seq.sortBy (fun (_,_,i) -> i)
            |> Seq.toList

        // Split out the supplied values and lambda parameters so that they can
        // be rearranged and recombined momentarily.
        let (args, parms) =
            args
            |> Seq.mapi (fun i x -> (i, x))
            |> Seq.choose
                (fun (i, x) ->
                    match x with
                    | AppliedValue _ -> Some (true , (i, x))
                    | LambdaParam  _ -> Some (false, (i, x))
                    | _ -> None
                )
            |> Seq.toList
            |> List.partition fst

        // Reverse the values passed in via function application, and then zip
        // them back up with the lambda parameters which they correspond to.
        // Create a map of the results based on the lambda parameter names, so
        // that they can be correlated with lambda variables in the union case
        // constructor call.
        let providedArgs =
            args
            |> Seq.map snd
            |> Seq.sortByDescending fst
            |> Seq.map
                (fun (_, x) ->
                    match x with
                    | AppliedValue x -> x
                    | _ -> failwithf "Got something other than AppliedValue in a place where only AppliedValue should exist."
                )
            |> Seq.zip parms
            |> Seq.map
                (fun ((_, (_, x)), y) ->
                    match x with
                    | LambdaParam x -> x, y
                    | _ -> failwithf "Got something other than LambdaParam in a place where only LambdaParam should exist."
                )
            |> Map.ofSeq

        // Take the argument information that goes into the union case
        // constructor, and for any arguments which were supplied, find them in
        // the map of provided arguments. For the arguments which were not
        // supplied, leave them as None, so that those fields can be matched
        // like wild-cards.
        let finishedArgs =
            actualArgs
            |> Seq.map
                (fun (v, f, i) ->
                    match v with
                    // Argument was provided
                    | Choice1Of2 v when providedArgs.ContainsKey v -> ((Some providedArgs.[v]), f, i)
                    // Argument was not provided
                    | Choice1Of2 _ -> (None, f, i)
                    // Literal value was provided directly to the union case
                    // ctor
                    | Choice2Of2 v -> (Some v, f, i)
                )
            |> Seq.sortBy (fun (_, _, i) -> i)
            |> Seq.map (fun (x, y, _) -> (x, y))
            |> Seq.toList

        { UnionCase = unionCase.Name; SuppliedArguments = finishedArgs; }

    /// <summary>
    /// Helper that takes an <see cref="Expr" /> value and returns a
    /// <see cref="UnionMetadata<'T>" /> value.
    /// </summary>
    /// <param name="e">
    /// The untyped quotation to process.
    /// </param>
    static member private ExprToMetadata e : UnionMetadata<_> = UnionMetadata<_>.ExprToUnionInfo e |> UnionMetadata<'T>.UnionInfoToMetadata

    // All of these overloads allow processing of wrappers for union cases of up
    // to 10 fields.

    /// <summary>
    /// Creates a new <see cref="UnionMetadata<'T>" /> value for the union type
    /// <typeparamref name="'T" />.
    /// </summary>
    /// <param name="e">
    /// A quotation for a union case of the type <typeparamref name="'T" />.
    /// </param>
    static member inline FromQuotation (e : Expr<'T>) = UnionMetadata<'T>.ExprToMetadata e
    /// <summary>
    /// Creates a new <see cref="UnionMetadata<'T>" /> value for the union type
    /// <typeparamref name="'T" />.
    /// </summary>
    /// <param name="e">
    /// A quotation for a function which takes one argument and returns a union
    /// case of the type <typeparamref name="'T" />.
    /// </param>
    static member inline FromQuotation (e : Expr<_ -> 'T>) = UnionMetadata<'T>.ExprToMetadata e
    /// <summary>
    /// Creates a new <see cref="UnionMetadata<'T>" /> value for the union type
    /// <typeparamref name="'T" />.
    /// </summary>
    /// <param name="e">
    /// A quotation for a function which takes two arguments and returns a union
    /// case of the type <typeparamref name="'T" />.
    /// </param>
    static member inline FromQuotation (e : Expr<_ -> _ -> 'T>) = UnionMetadata<'T>.ExprToMetadata e
    /// <summary>
    /// Creates a new <see cref="UnionMetadata<'T>" /> value for the union type
    /// <typeparamref name="'T" />.
    /// </summary>
    /// <param name="e">
    /// A quotation for a function which takes three arguments and returns a
    /// union case of the type <typeparamref name="'T" />.
    /// </param>
    static member inline FromQuotation (e : Expr<_ -> _ -> _ -> 'T>) = UnionMetadata<'T>.ExprToMetadata e
    /// <summary>
    /// Creates a new <see cref="UnionMetadata<'T>" /> value for the union type
    /// <typeparamref name="'T" />.
    /// </summary>
    /// <param name="e">
    /// A quotation for a function which takes four arguments and returns a
    /// union case of the type <typeparamref name="'T" />.
    /// </param>
    static member inline FromQuotation (e : Expr<_ -> _ -> _ -> _ -> 'T>) = UnionMetadata<'T>.ExprToMetadata e
    /// <summary>
    /// Creates a new <see cref="UnionMetadata<'T>" /> value for the union type
    /// <typeparamref name="'T" />.
    /// </summary>
    /// <param name="e">
    /// A quotation for a function which takes five arguments and returns a
    /// union case of the type <typeparamref name="'T" />.
    /// </param>
    static member inline FromQuotation (e : Expr<_ -> _ -> _ -> _ -> _ -> 'T>) = UnionMetadata<'T>.ExprToMetadata e
    /// <summary>
    /// Creates a new <see cref="UnionMetadata<'T>" /> value for the union type
    /// <typeparamref name="'T" />.
    /// </summary>
    /// <param name="e">
    /// A quotation for a function which takes six arguments and returns a union
    /// case of the type <typeparamref name="'T" />.
    /// </param>
    static member inline FromQuotation (e : Expr<_ -> _ -> _ -> _ -> _ -> _ -> 'T>) = UnionMetadata<'T>.ExprToMetadata e
    /// <summary>
    /// Creates a new <see cref="UnionMetadata<'T>" /> value for the union type
    /// <typeparamref name="'T" />.
    /// </summary>
    /// <param name="e">
    /// A quotation for a function which takes seven arguments and returns a
    /// union case of the type <typeparamref name="'T" />.
    /// </param>
    static member inline FromQuotation (e : Expr<_ -> _ -> _ -> _ -> _ -> _ -> _ -> 'T>) = UnionMetadata<'T>.ExprToMetadata e
    /// <summary>
    /// Creates a new <see cref="UnionMetadata<'T>" /> value for the union type
    /// <typeparamref name="'T" />.
    /// </summary>
    /// <param name="e">
    /// A quotation for a function which takes eight arguments and returns a
    /// union case of the type <typeparamref name="'T" />.
    /// </param>
    static member inline FromQuotation (e : Expr<_ -> _ -> _ -> _ -> _ -> _ -> _ -> _ -> 'T>) = UnionMetadata<'T>.ExprToMetadata e
    /// <summary>
    /// Creates a new <see cref="UnionMetadata<'T>" /> value for the union type
    /// <typeparamref name="'T" />.
    /// </summary>
    /// <param name="e">
    /// A quotation for a function which takes nine arguments and returns a
    /// union case of the type <typeparamref name="'T" />.
    /// </param>
    static member inline FromQuotation (e : Expr<_ -> _ -> _ -> _ -> _ -> _ -> _ -> _ -> _ -> 'T>) = UnionMetadata<'T>.ExprToMetadata e
    /// <summary>
    /// Creates a new <see cref="UnionMetadata<'T>" /> value for the union type
    /// <typeparamref name="'T" />.
    /// </summary>
    /// <param name="e">
    /// A quotation for a function which takes ten arguments and returns a union
    /// case of the type <typeparamref name="'T" />.
    /// </param>
    static member inline FromQuotation (e : Expr<_ -> _ -> _ -> _ -> _ -> _ -> _ -> _ -> _ -> _ -> 'T>) = UnionMetadata<'T>.ExprToMetadata e
