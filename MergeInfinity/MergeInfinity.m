(* ::Package:: *)

Package["MergeInfinity`"]


PackageImport["SilviaCollection`"]


PackageExport["MergeInfinity"]
PackageExport["AssociationAlign"]
PackageExport["AssociationLousyDiff"]
PackageExport["AssociationStrictDiff"]


MergeInfinity[asso : {__Association}, func_] :=
 Module[{$mergeInfty, $func}
  ,
  $func[{e_}] := e;
  $func[e_List] := func[e]
  ;
  $mergeInfty[e : {__Association}] := Merge[e, $mergeInfty];
  $mergeInfty[e_List] := $func[e]
  ;
  $mergeInfty@asso
  ]
MergeInfinity[func_] := MergeInfinity[#, func] &


AssociationAlign[config_Association: <||>] :=
 Module[{default = <|"null" -> "\[FilledVerySmallSquare]"|>, null},
  null = {config, default} // Merge[First] // #["null"] &;
  RightComposition[
   branch[Identity,
    RightComposition[
     MergeInfinity[null &]
     , branch[Identity,
      Position[#, e_ /; e =!= null && Head[e] =!= Association, 
         Heads -> False] & /* Map[# -> null &]
      ]
     , Apply[ReplacePart]
     ]
    ]
   , Apply[Function[{orig, template},
     MergeInfinity[First][{#, template}] & /@ orig
     ]]
   ]
  ]


AssociationLousyDiff[config_Association: <||>] :=
 Module[{default = <|"test" -> SameQ|>, testfunc},
  testfunc = {config, default} // Merge[First] // #["test"] &
  ;
  RightComposition[
   MergeInfinity[Apply[If[testfunc[##], <||>, {##}] &]]
   , <|"root" -> #|> &
   , RightComposition[
     branch[Identity, Position[<||>]]
     , Apply[
      Function[{assoc, pos},
        ReplacePart[assoc,
         Most[pos] -> KeyDrop[Extract[assoc, Most[pos]], Last[pos]]
         ]
        ] // Curry[Fold, {1, 2, 3}]]
     ] // Curry[FixedPoint, {1, 2}]
   , #["root"] &
   ]
  ]


AssociationStrictDiff[config_Association: <||>] :=
 Module[{default = <|"test" -> SameQ, 
     "null" -> "\[FilledVerySmallSquare]"|>, testfunc, assocdiffNull},
  {testfunc, assocdiffNull} =
   {config, default} // Merge[First] // Lookup[{"test", "null"}]
  ;
  RightComposition[
   AssociationAlign[<|"null" -> assocdiffNull|>]
   , AssociationLousyDiff[<|"test" -> testfunc|>]
   ]
  ]
