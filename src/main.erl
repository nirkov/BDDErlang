%%%-------------------------------------------------------------------
%%% @author nirkov
%%% @copyright (C) 2019, <COMPANY>
%%% @doc
%%%
%%% @end
%%% Created : 21. Apr 2019 12:15
%%%-------------------------------------------------------------------
-module(main).
-author("nirkov").

%% API
-import(lists,[max/1]).

-export([exp_to_bdd/2, testing/0]).

%% --------------------------------------------------------------------------------------------------
%%                             ****          Records         ****
%% --------------------------------------------------------------------------------------------------

-record(node, {symbol, leftSon, rightSon, height}).
-record(tree, {variable_permutation, root}).

new_node(FatherSymbol, LeftSon, RightSon, Height)->
  #node{symbol = FatherSymbol,leftSon = LeftSon, rightSon = RightSon, height = Height}.

new_tree(Variable_permutation, Construction)->
  #tree{variable_permutation = Variable_permutation, root = Construction}.


%% --------------------------------------------------------------------------------------------------
%%                          ****      The Project Functions       ****
%% --------------------------------------------------------------------------------------------------

exp_to_bdd(BoolFunc, Order)->

  % take all variable from the function.
  Variables = parsing_from_Parenthesis(BoolFunc),

  % Delete duplicate of variable
  DifferentVariables = deletDuplicate(Variables),

  % make all permutation of the variable
  BinaryVariablePermutation = permutationSets(DifferentVariables),

  % build the tree for any permutation of the binary variable

  BinaryTrees = [new_tree(Permutation, binaryTree(Permutation, BoolFunc)) || Permutation <- BinaryVariablePermutation],

  case Order of
    tree_height  ->  min_tree_height(BinaryTrees);
    num_of_nodes ->  min_num_of_nodes(BinaryTrees);
    num_of_leafs ->  min_num_of_leafs(BinaryTrees);
    _ -> BinaryTrees
  end.



solve_bdd(BDDTree, VariableList)->
  solve_bdd_bool(BDDTree#tree.root, maps:from_list(VariableList)).

solve_bdd_bool(Root, VarMap)->
  NodeVal = maps:get(Root#node.symbol ,VarMap),

  if
    (NodeVal =:= false) or (NodeVal =:= 0) -> % if the root variable value is false we check his left child
       if
         (Root#node.leftSon =:= true) or (Root#node.leftSon =:= false) -> Root#node.leftSon; % if his child result we return it
         true -> solve_bdd_bool(Root#node.leftSon, VarMap)                                   % else we down to the sub tree rooted in this child
       end;
    true ->
       if    % if the root variable value is true we check his right child
         (Root#node.rightSon =:= true) or (Root#node.rightSon =:= false) -> Root#node.rightSon;  % if his child result we return it
         true -> solve_bdd_bool(Root#node.rightSon, VarMap)                                      % else we down to the sub tree rooted in this child
       end
  end.


solve_for_all_possible(Tree)->
  AllPossible = [[ {x1, false},{x2, false},{x3, false},{x4, false}],
                  [{x1, false},{x2, false},{x3, false},{x4, true}],
                  [{x1, false},{x2, false},{x3, true} ,{x4, false}],
                  [{x1, false},{x2, false},{x3, true} ,{x4, true}],
                  [{x1, false},{x2, true} ,{x3, false},{x4, false}],
                  [{x1, false},{x2, true} ,{x3, false},{x4, true}],
                  [{x1, false},{x2, true} ,{x3, true} ,{x4, false}],
                  [{x1, false},{x2, true} ,{x3, true} ,{x4, true}],
                  [{x1, true} ,{x2, false},{x3, false},{x4, false}],
                  [{x1, true} ,{x2, false},{x3, false},{x4, true}],
                  [{x1, true} ,{x2, false},{x3, true} ,{x4, false}],
                  [{x1, true} ,{x2, false},{x3, true} ,{x4, true}],
                  [{x1, true} ,{x2, true} ,{x3, false},{x4, false}],
                  [{x1, true} ,{x2, true} ,{x3, false},{x4, true}],
                  [{x1, true} ,{x2, true} ,{x3, true} ,{x4, false}],
                  [{x1, true} ,{x2, true} ,{x3, true} ,{x4, true}]],


  Z = [{X, solve_bdd(Tree, X)} || X <- AllPossible].




testing()->
%%  Test solve booleam function
%%  X1 = solve_bdd({tree,[x1,x3,x4,x2],{node,x1,true,{node,x3,{node,x4,true,{node,x2,true,false}},true}}},[{x2, true},{x3, 0},{x1, true},{x4, true}]),
%%  print("number of nodes : ", X1),
%%  X2 = solve_bdd({tree,[x1,x3,x4,x2],{node,x1,true,{node,x3,{node,x4,true,{node,x2,true,false}},true}}},[{x2, true},{x3, true},{x1, false},{x4, false}]),
%%  print("number of nodes : ", X2),
%%  X3 = solve_bdd({tree,[x1,x3,x4,x2],{node,x1,true,{node,x3,{node,x4,true,{node,x2,true,false}},true}}},[{x2, false},{x3, false},{x1, true},{x4, true}]),
%%  print("number of nodes : ", X3),
%%
%%  Test calc number of nodes
%%  NumNode1 = num_of_node({node,x4,
%%                         {node,x1,
%%      {node,x3,{node,x2,false,true,1},false,2},
%%      {node,x3,{node,x2,false,true,1},true,2},
%%      3},
%%    true,4}),
%%
%%  print("number of nodes : ", NumNode1),
%%
%%  NumNode2 = num_of_node({node,x3,
%%    {node,x4,{node,x2,false,true,1},true,2},
%%    {node,x1,{node,x4,false,true,1},true,2},
%%    3}),
%%
%%  print("number of nodes : ", NumNode2).
%%
%%  Test calc number of leaf
%%  NumLeafe1 = num_of_leafs({node,x4,
%%                         {node,x1,
%%      {node,x3,{node,x2,false,true,1},false,2},
%%      {node,x3,{node,x2,false,true,1},true,2},
%%      3},
%%    true,4}),
%%
%%  print("number of leaf : ", NumLeafe1),
%%
%%  NumLeafe2 = num_of_leafs({node,x4,true,
%%  {node,x3,{node,x1,true,{node,x2,true,false,1},2},true,3},
%%  4}),
%%
%%  print("number of leaf : ", NumLeafe2),
%%
%%  NumLeafe3 = num_of_leafs({node,x4,true,
%%  {node,x3,{node,x1,true,{node,x2,true,false,1},2},true,3},
%%  4}),
%%
%%  print("number of leaf : ", NumLeafe3),
%%
%%  NumLeafe4 = num_of_leafs({node,x1,true,
%%  {node,x2,true,{node,x4,true,{node,x3,false,true,1},2},3},
%%  4}),
%%
%%  print("number of leaf : ", NumLeafe4).
%%  {'or',{ {'or',{ {'and',{ x2 , {'not', x3} }} , {'and',{ x1 , x3 }} }} , x4 }}


  Part_A = {'and',{ {'and',{x1,x3}}, {'not',x2}}},
  Part_B = {'not',{'and',{ x1, x4 } } },
  Part_C = {'not',  {'and',{ {'and',{x1, {'not',x3} }}, {'or',{x2, {'not',x4} }}}}},
  F_x1_x2_x3_x4 = {'or', {Part_C, {'or', {Part_A, Part_B}}}},

  % Test ORDER : tree_height

  StartTime_tree_height = now(),
  Tree_tree_height = exp_to_bdd(F_x1_x2_x3_x4, tree_height),
  EndTime_tree_height = now(),
  print("ORDER : tree_height. Time take to create BBD : ", timer:now_diff(EndTime_tree_height, StartTime_tree_height) / 1000),
  StartTimeSolve_tree_height = now(),
  AllPossibleResult_tree_height = solve_for_all_possible(Tree_tree_height),
  EndTimeSolve_tree_height = now(),
  print("ORDER : tree_height. Solve time of all possible assigment : ", timer:now_diff(EndTimeSolve_tree_height, StartTimeSolve_tree_height) / 1000),
  print("", AllPossibleResult_tree_height),
  print("~n",""),
  print("~n",""),

  % Test ORDER : num_of_nodes

  StartTime_num_of_nodes = now(),
  Tree_num_of_nodes = exp_to_bdd(F_x1_x2_x3_x4, num_of_nodes),
  EndTime_num_of_nodes = now(),
  print("ORDER : num_of_nodes. Time take to create BBD",timer:now_diff(EndTime_num_of_nodes, StartTime_num_of_nodes) / 1000),

  StartTimeSolve_num_of_nodes = now(),
  AllPossibleResult_num_of_nodes = solve_for_all_possible(Tree_num_of_nodes),
  EndTimeSolve_num_of_nodes = now(),
  print("ORDER : num_of_nodes. Solve time of all possible assigment : ", timer:now_diff(EndTimeSolve_num_of_nodes, StartTimeSolve_num_of_nodes) / 1000),
  print("", AllPossibleResult_num_of_nodes),
  print("~n",""),
  print("~n",""),

% Test ORDER : num_of_leafs

  StartTime_num_of_leafs = now(),
  Tree_num_of_leafs = exp_to_bdd(F_x1_x2_x3_x4, num_of_leafs),
  EndTime_num_of_leafs = now(),
  print("ORDER : num_of_leafs. Time take to create BBD", timer:now_diff(EndTime_num_of_leafs, StartTime_num_of_leafs) / 1000),

  StartTimeSolve_num_of_leafs = now(),
  AllPossibleResult_num_of_leafs = solve_for_all_possible(Tree_num_of_leafs),
  EndTimeSolve_num_of_leafs = now(),
  print("ORDER : num_of_leafs. Solve time of all possible assigment : ", timer:now_diff(EndTimeSolve_num_of_leafs, StartTimeSolve_num_of_leafs) / 1000),
  print("", AllPossibleResult_num_of_leafs)
.



%% --------------------------------------------------------------------------------------------------
%% --------------------------------------------------------------------------------------------------

%                                          UTIL FUNCTIONS

%% --------------------------------------------------------------------------------------------------
%% --------------------------------------------------------------------------------------------------



% print function
print(Msg, Object)-> io:fwrite(Msg ++ "~p~n", [Object]).

% Take all variable.
parsing_from_Parenthesis({'not', A}) -> parsing_from_Parenthesis(A);
parsing_from_Parenthesis({_, {A, B}}) -> parsing_from_Parenthesis(A) ++  parsing_from_Parenthesis(B);
parsing_from_Parenthesis(A)-> [A].

% Make all permutations.
permutationSets([]) -> [[]];
% for any H, we take the all permutation of T, Recursively.
permutationSets(List)  -> [[H|T] || H <- List, T <- permutationSets(List--[H])].

% Delete duplicate in list.
deletDuplicate([])-> [];
deletDuplicate([H|T]) -> [H | [X || X <-deletDuplicate(T), X =/= H]].

%% --------------------------------------------------------------------------------------------------
%%                              ****     Build the binary tree     ****
%% --------------------------------------------------------------------------------------------------

% Build a tree recursively and merge between identically nodes in same high.
binaryTree([H], BoolFunc)->
  R = calculateBooleanFunction(replace(BoolFunc, H, true)) , % stop condition - this is leafs so we already replace all
  L = calculateBooleanFunction(replace(BoolFunc, H, false)), %                  the variable with value and need to calculate the function.
  if
    R=/=L -> new_node(H, L, R, 1);  % if the left result not equal to the right, we need new node and take both cases into account
    true -> L                       % Rule 1 : both cases equals - we eliminate the node so we merge the cases.
  end;

binaryTree([H|T], BoolFunc)->
  R = binaryTree(T, replace(BoolFunc, H, true)) ,
  L = binaryTree(T, replace(BoolFunc, H, false)),
  if
    R=/=L -> if
               % R not a node so the height of the root to this sub tree  = L.height + 1
               (is_record(L, node) and (not is_record(R, node))) -> new_node(H, L, R, L#node.height + 1);

                % L not a node so the height of the root to this sub tree  = R.height + 1
               (is_record(R, node) and (not is_record(L, node))) -> new_node(H, L, R, R#node.height + 1);

               % Both R and L nodes so the height of thiere father  =  Max{R.height, L.height} + 1
               (is_record(L, node) and  is_record(R, node))      -> new_node(H, L, R, max([L#node.height, R#node.height]) + 1);

               % Both are boolean answer of the BoolFunc
               true -> new_node(H, L, R, 1)
             end;
    true ->  L
  end.

%% --------------------------------------------------------------------------------------------------
%%                ****   Calculate the boolean function after replace all variable   ****
%% --------------------------------------------------------------------------------------------------


% Calculate boolean function
% All the variable already replace to True or Flase value so we can calculate the logical answer of this assignment
calculateBooleanFunction(BoolFunc)->
  case BoolFunc of
    {'not', X}     -> not calculateBooleanFunction(X);
    {'and',{X, Y}} -> calculateBooleanFunction(X) and calculateBooleanFunction(Y);
    {'or' ,{X, Y}} -> calculateBooleanFunction(X) or  calculateBooleanFunction(Y);
    _ -> BoolFunc
  end.

%% --------------------------------------------------------------------------------------------------
%%                     ****   Replace boolean variables with values      ****
%% --------------------------------------------------------------------------------------------------


% Replace variable with value (true or false)
% assignment of given value to the given variable and build the boolean function with the assignment
replace({'not', X}, Variable, Value)->
  if
    X =:= Variable -> not Value;
    true -> {'not', replace(X, Variable, Value)}
  end;


replace({'or',{X, Y}}, Variable, Value)->
  if
    (X =:= Variable) and  (Y =:= Variable) -> Value;
    X =:= Variable -> {'or',{Value, replace(Y, Variable, Value)}};
    Y =:= Variable -> {'or',{replace(X, Variable, Value), Value}};
    true -> {'or', {replace(X, Variable, Value) , replace(Y, Variable, Value)}}
  end;

replace({'and',{X, Y}}, Variable, Value)->
  if
    (X =:= Variable) and  (Y =:= Variable) -> Value;
    X =:= Variable -> {'and',{Value, replace(Y, Variable, Value)}};
    Y =:= Variable -> {'and',{replace(X, Variable, Value), Value}};
    true -> {'and', {replace(X, Variable, Value) , replace(Y, Variable, Value)}}
  end;

replace(X, Variable, Value)->
  if
    X =:= Variable -> Value;
    true -> X
  end.

%% --------------------------------------------------------------------------------------------------
%%                         ****     Find minimum highest tree        ****
%% --------------------------------------------------------------------------------------------------

min_tree_height([])-> [];
min_tree_height([H|T]) -> find_min_tree(H, T).

find_min_tree(MinTree, [])-> MinTree;
find_min_tree(MinTree, [H|T]) ->
  if
    H#tree.root#node.height < MinTree#tree.root#node.height -> find_min_tree(H, T);
    true ->  find_min_tree(MinTree, T)
  end.

%% --------------------------------------------------------------------------------------------------
%%                         ****     Find tree with minimum nodes     ****
%% --------------------------------------------------------------------------------------------------

min_num_of_nodes([]) -> [];
min_num_of_nodes([H|T])-> find_min_num_of_nodes(H, T).

find_min_num_of_nodes(MinNumNode, [])-> MinNumNode;
find_min_num_of_nodes(MinNumNode, [H|T])->
  NumNodeInOptimalTree = num_of_node(MinNumNode#tree.root),
  NumNodeInTestingTree = num_of_node(H#tree.root),
  if
    NumNodeInTestingTree < NumNodeInOptimalTree-> find_min_num_of_nodes(H, T);
    true ->  find_min_num_of_nodes(MinNumNode, T)
  end.

num_of_node(Root)->
  if
    is_record(Root#node.rightSon, node) and  is_record(Root#node.leftSon, node)
      -> 1 + num_of_node(Root#node.rightSon) + num_of_node(Root#node.leftSon);

    is_record(Root#node.rightSon, node) -> 1 + num_of_node(Root#node.rightSon);

    is_record(Root#node.leftSon, node)  -> 1 + num_of_node(Root#node.leftSon);

    true -> 1
  end.

%% --------------------------------------------------------------------------------------------------
%%                         ****      Find tree with minimum leafs    ****
%% --------------------------------------------------------------------------------------------------

min_num_of_leafs([]) -> [];
min_num_of_leafs([H|T])-> find_min_num_of_leafs(H, T).

find_min_num_of_leafs(MinNumLeaf, [])-> MinNumLeaf;
find_min_num_of_leafs(MinNumLeaf, [H|T])->
  NumLeafInOptimalTree = num_of_leafs(MinNumLeaf#tree.root),
  NumLeafInTestingTree = num_of_leafs(H#tree.root),
  if
    NumLeafInTestingTree < NumLeafInOptimalTree -> find_min_num_of_leafs(H, T);
    true ->  find_min_num_of_leafs(MinNumLeaf, T)
  end.

num_of_leafs(Root)->
  if
    is_record(Root#node.rightSon, node) and  is_record(Root#node.leftSon, node)
      -> num_of_leafs(Root#node.rightSon) + num_of_leafs(Root#node.leftSon);

    is_record(Root#node.rightSon, node) -> num_of_leafs(Root#node.rightSon);

    is_record(Root#node.leftSon, node)  -> num_of_leafs(Root#node.leftSon);

    true -> 1
  end.