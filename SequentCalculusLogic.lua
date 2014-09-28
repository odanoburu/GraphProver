--[[

   Sequent Calculus Module

   Authors: Vitor, Bruno, Hermann, Jefferson
]]--

require "SequentGoalsLogic"
require "ConstantsForSequent"
require "logging" 
require "logging.file"

local logger = logging.file("aux/prover%s.log", "%Y-%m-%d")
logger:setLevel(logging.INFO)

LogicModule = {}

local GoalSequentNode = nil
local serializedSequent = ""

-- Private functions

local function createNewSequent(graph, sequentNode)
   local copiedSequent = nil

   local listNewNodes = {}
   local listNewEdges = {}
   
   nodeSeqNew = SequentNode:new(sequentNode:getInformation("type"))
   listNewNodes[#listNewNodes+1] = nodeSeqNew
   

   local newNodeLeft = SequentNode:new(lblNodeEsq)
   local newNodeDir = SequentNode:new(lblNodeDir)
   listNewNodes[#listNewNodes+1] = newNodeLeft
   listNewNodes[#listNewNodes+1] = newNodeDir

   local newEdgeLeft = SequentEdge:new(lblEdgeEsq, nodeSeqNew, newNodeLeft)             
   local newEdgeRight = SequentEdge:new(lblEdgeDir, nodeSeqNew, newNodeDir)
   listNewEdges[#listNewEdges+1] = newEdgeLeft
   listNewEdges[#listNewEdges+1] = newEdgeRight
   
   local nodeEsq = sequentNode:getEdgeOut(lblEdgeEsq):getDestino()
   local nodeDir = sequentNode:getEdgeOut(lblEdgeDir):getDestino()
   
   esqEdgesOut = nodeEsq:getEdgesOut()
   for i=1, #esqEdgesOut do
      local newEdge = SequentEdge:new(esqEdgesOut[i]:getLabel(), newNodeLeft, esqEdgesOut[i]:getDestino())
      listNewEdges[#listNewEdges+1] = newEdge
   end

   dirEdgesOut = nodeDir:getEdgesOut()
   for i=1, #dirEdgesOut do
      local newEdge = SequentEdge:new(dirEdgesOut[i]:getLabel(), newNodeDir, dirEdgesOut[i]:getDestino())
      listNewEdges[#listNewEdges+1] = newEdge
   end  

   return nodeSeqNew,listNewNodes,listNewEdges

end

local function createGraphImplyeft()
   
   local SequentGraph = Graph:new ()
   
   NodeGG = SequentNode:new(lblNodeGG)
   NodeSeq = SequentNode:new(opSeq.graph)
   NodeEsq = SequentNode:new(lblNodeEsq)
   NodeDir = SequentNode:new(lblNodeDir)
   
   NodeF = SequentNode:new('F')
   NodeImp0 = SequentNode:new(opImp.graph)
   NodeA = SequentNode:new('A')

   Edge1 = SequentEdge:new(lblEdgeGoal, NodeGG, NodeSeq)
   Edge2 = SequentEdge:new(lblEdgeEsq, NodeSeq, NodeEsq)
   Edge3 = SequentEdge:new(lblEdgeDir, NodeSeq, NodeDir)
   Edge4 = SequentEdge:new('', NodeEsq, NodeF)
   Edge5 = SequentEdge:new('', NodeEsq, NodeA)
   Edge6 = SequentEdge:new('', NodeDir, NodeImp0)
   Edge7 = SequentEdge:new(lblEdgeEsq , NodeImp0, NodeF)
   Edge8 = SequentEdge:new(lblEdgeDir , NodeImp0, NodeA)

   nodes = {NodeGG, NodeSeq, NodeEsq, NodeDir, NodeImp0, NodeF, NodeA}
   edges = {Edge1, Edge2, Edge3, Edge4, Edge5, Edge6, Edge7, Edge8}

   SequentGraph:addNodes(nodes)
   SequentGraph:addEdges(edges)

   goalsList[NodeSeq:getLabel()] = GoalsLogic.assembleGoalList(NodeSeq)
   return SequentGraph
end

local function createGraphEmpty()

   local SequentGraph = Graph:new ()
   
   local NodeGG = SequentNode:new(lblNodeGG)
   local nodes = {NodeGG}
   local edges = {}
   
   SequentGraph:addNodes(nodes)
   SequentGraph:addEdges(edges)
   SequentGraph:setRoot(NodeGG)
   return SequentGraph
end

---
--- @param letters Stores all atoms.  
local function createGraphFormula(formula_tabela,letters)

   local S2
   local S1
   local nodes
   local edges
   local FormulaGraph = Graph:new ()
   local NodeLetter=nil
   
   createDebugMessage("tabela ="..formula_tabela.tag)


   if formula_tabela.tag == "Atom" then 
      local prop_letter = formula_tabela["1"]
      for k,v in pairs(letters) do 
         if k == prop_letter then 
            NodeLetter = v
         end
      end
      if not NodeLetter then   
         NodeLetter = SequentNode:new(prop_letter)
         letters[prop_letter]=NodeLetter
      end
      
      nodes={NodeLetter}
      edges={}
      FormulaGraph:addNodes(nodes)
      FormulaGraph:addEdges(edges)
      FormulaGraph:setRoot(NodeLetter)
      
   elseif formula_tabela.tag == "imp" then

      S1,letters= createGraphFormula(formula_tabela["1"],letters)
      S2,letters = createGraphFormula(formula_tabela["2"],letters)

      local NodeImp = SequentNode:new(opImp.graph)
      createDebugMessage("S1 ="..S1.root:getLabel())
      createDebugMessage("S2 ="..S2.root:getLabel())
      local EdgeEsq = SequentEdge:new(lblEdgeEsq, NodeImp, S1.root)
      local EdgeDir = SequentEdge:new(lblEdgeDir, NodeImp, S2.root)
      nodes = {NodeImp}
      edges = {EdgeEsq,EdgeDir}

      FormulaGraph:addNodes(S1.nodes)
      FormulaGraph:addNodes(S2.nodes)
      FormulaGraph:addNodes(nodes)
      FormulaGraph:addEdges(S1.edges)
      FormulaGraph:addEdges(S2.edges)
      FormulaGraph:addEdges(edges)
      FormulaGraph:setRoot(NodeImp)           
   end

   return FormulaGraph,letters
end   

local function createGraphSequent(seq_tabela, letters)

   local goalsList={}
   local SequentGraph = Graph:new ()
   local S,L
   local NodeGG = SequentNode:new(lblNodeGG)
   local NodeSeq = SequentNode:new(opSeq.graph)
   local NodeEsq = SequentNode:new(lblNodeEsq)
   local NodeDir = SequentNode:new(lblNodeDir)
   local NodeBrackets = SequentNode:new(lblNodeBrackets)
   S,L = createGraphFormula(seq_tabela, letters)

   createDebugMessage("RootNode ="..S.root:getLabel())

   local Edge1 = SequentEdge:new(lblEdgeGoal, NodeGG, NodeSeq)
   local Edge2 = SequentEdge:new(lblEdgeEsq, NodeSeq, NodeEsq)
   local Edge3 = SequentEdge:new(lblEdgeDir, NodeSeq, NodeDir)
   local Edge4 = SequentEdge:new('', NodeDir, S.root)
   local Edge5 = SequentEdge:new('', NodeDir, NodeBrackets)

   local nodes = {NodeGG, NodeSeq, NodeDir, NodeEsq, NodeBrackets}
   SequentGraph:addNodes(nodes)
   SequentGraph:addNodes(S.nodes)
   local edges = {Edge1, Edge2, Edge3, Edge4, Edge5}    
   SequentGraph:addEdges(edges)
   SequentGraph:addEdges(S.edges)

   goalsList[NodeSeq:getLabel()] = GoalsLogic.assembleGoalList(NodeSeq)
   return SequentGraph, goalsList
end

local function expandNodeAtomic(graph, sequentNode, node)
   local edgesLeft = sequentNode:getEdgeOut(lblEdgeEsq):getDestino():getEdgesOut()
   local rightFormulaNode = sequentNode:getEdgeOut(lblEdgeDir):getDestino():getEdgeOut("0"):getDestino()
--   local formulasInBracketNode = sequentNode:getEdgeOut(lblEdgeDir):getDestino():getEdgeOut("1"):getDestino():getEdgesOut()
   local side = " "
   local isAxiom = false

   for i=1, #edgesLeft do
      if edgesLeft[i]:getDestino():getLabel() == node:getLabel() then
         side = "Left"
         break
      end
   end 
   if side == "Left" then 
      if rightFormulaNode:getLabel() == node:getLabel() then 
         isAxiom = true
      -- else
      --    for i=1, #formulasInBracketNode do
      --       if formulasInBracketNode[i]:getDestino():getLabel() == node:getLabel() then
      --          isAxiom = true
      --          break
      --       end
      --    end
      end
   end 
   if isAxiom then
      sequentNode:setInformation("isAxiom", true)
      return true, graph 
   else 
      return false, graph
   end
end

local function expandNodeImp(graph, sequentNode, nodeOpImp)

   local sideOfOperator = LogicModule.verifySideOfOperator(sequentNode, nodeOpImp)      

   if sideOfOperator == leftSide then
      return LogicModule.expandNodeImpLeft(graph, sequentNode, nodeOpImp)
   elseif sideOfOperator == rightSide then
      return LogicModule.expandNodeImpRight(graph, sequentNode, nodeOpImp)
   elseif sideOfOperator == nil then
      return nil
   end          

   return graph
end

local function verifySideOfSequent(originNode, targetNode)
   edgesOut = originNode:getEdgesOut()

   if edgesOut == nil then
      return false
   end

   local retValues = {}

   for i=1, #edgesOut do
      if edgesOut[i]:getDestino():getLabel() == targetNode:getLabel() then
         return true
      end
   end

   return false
end

local function generateCounterModel(sequentNode, counterModel)

   if counterModel == nil then
      -- iniciar table
   end 

   local nodeLeft = sequentNode:getEdgeOut(lblEdgeLeft):getDestino()
   local nodeRight = sequentNode:getEdgeOut(lblEdgeDir):getDestino()
   
   local listEdgesOut = nodeLeft:getEdgesOut()
   for i=1, #listEdgesOut do
      -- estende table (satisfaz) com listEdgesOut[i]:getDestino():getLabel()
   end

   local outsideBrackets = nodeRight:getEdgeOut("0"):getDestino()
   -- estende table (não satisfaz) com outsideBrackets:getLabel()

   local nodeBrackets = nodeRight:getEdgeOut("1"):getDestino()  
   local listEdgesOut = nodeBrackets:getEdgesOut()
   for i=1, #listEdgesOut do
      -- estende table (não satisfaz) com listEdgesOut[i]:getDestino():getLabel()
   end
   
   return counterModel

end

local function markProvedSequent(sequentNode)
   assert( getmetatable(sequentNode) == Node_Metatable , "markProvedSequent expects a node.")

   local allBrachesProved = false

   if sequentNode:getInformation("isAxiom") == nil then
      local deductions = sequentNode:getEdgesOut()

      for i=1, #deductions do
         if deductions[i]:getLabel() == lblEdgeDeducao then
            if markProvedSequent(deductions[i]:getDestino()) == false then
               allBrachesProved = false
            else
               allBrachesProved = true
            end
         end
      end       
   else
      allBrachesProved = true
   end

   if allBrachesProved then
      sequentNode:setInformation("isProved", true)
      return true
   else
      sequentNode:setInformation("isProved", false)
      return false
   end
end

local function countGraphElements(graph) 
   local countNodeElements = {}
   local countEdgesElements = {}  

   nodes = graph:getNodes()

   for i=1, #nodes do   
      if countNodeElements[nodes[i]:getInformation("type")] == nil then
         countNodeElements[nodes[i]:getInformation("type")] = 1
      else
         countNodeElements[nodes[i]:getInformation("type")] = countNodeElements[nodes[i]:getInformation("type")] + 1
      end
   end

   edges = graph:getEdges()

   for i=1, #edges do   
      if countEdgesElements[edges[i]:getLabel()] == nil then
         countEdgesElements[edges[i]:getLabel()] = 1
      else
         countEdgesElements[edges[i]:getLabel()] = countEdgesElements[edges[i]:getLabel()] + 1
      end
   end  

   for k,count in pairs(countNodeElements) do
      logger:info("statistics -- Total nodes of type "..k.." is "..count)
   end

   for k,count in pairs(countEdgesElements) do
      logger:info("statistics -- Total nodes of type "..k.." is "..count)
   end

end

local function printFormula(formula)
   local ret = ""
   local edge, subformula = nil

   if (formula:getEdgesOut() ~= nil) and (#formula:getEdgesOut() ~= 0) then
      if formula:getLabel():sub(1,2) == lblNodeBrackets then
         ret = ret.."["
         for i, edge in ipairs(formula:getEdgesOut()) do
            subformula = edge:getDestino()
            ret = ret..printFormula(subformula)..","
         end
         ret = ret:sub(1, ret:len()-1)
         ret = ret.."]"
      else
         for i, edge in ipairs(formula:getEdgesOut()) do
            if edge:getLabel() == lblEdgeEsq then
               subformula = edge:getDestino()
               ret = ret.."("..printFormula(subformula)
            end
         end    

         ret = ret.." "..opImp.tex.." "

         for i, edge in ipairs(formula:getEdgesOut()) do
            if edge:getLabel() == lblEdgeDir then
               subformula = edge:getDestino()
               ret = ret..printFormula(subformula)..")"
            end
         end    
      end
   else
      ret = formula:getLabel()
      if formula:getLabel():sub(1,2) == lblNodeBrackets then
         ret = ret:sub(1, ret:len()-1)
      end
   end

   return ret

end

local function printSequent(seq, file)
   local ret = ""
   local edge, nodeEsq, nodeDir = nil
   local deductions = {}
   local j = 1

   if seq ~= nil then           
      for i, edge in ipairs(seq:getEdgesOut()) do       
         if edge:getLabel() == lblEdgeEsq then
            nodeEsq = edge:getDestino()
         end
         if edge:getLabel() == lblEdgeDir then
            nodeDir = edge:getDestino()
         end
         if edge:getLabel() == lblEdgeDeducao then
            seq = edge:getDestino()
            deductions[j] = seq
            j = j+1
         end                    
      end

      if #deductions > 0 then
         file:write("\\infer\n")
      end

      file:write("{")
      if nodeEsq ~= nil then
         for i, edge in ipairs(nodeEsq:getEdgesOut()) do
            ret = ret..printFormula(edge:getDestino())
            ret = ret..","
         end    
         ret = ret:sub(1, ret:len()-1)
      end

      ret = ret.." "..opSeq.tex.." "

      edge = nil
      for i, edge in ipairs(nodeDir:getEdgesOut()) do
         ret = ret..printFormula(edge:getDestino())
         ret = ret..","
      end       
      ret = ret:sub(1, ret:len()-1)     

      file:write(ret)
      file:write("}")   
      serializedSequent = serializedSequent..ret.." "  


      if #deductions > 0 then
         serializedSequent = serializedSequent:sub(1, serializedSequent:len()-1)
         serializedSequent = serializedSequent.."|"
         file:write("\n{\n")

         for i, edge in ipairs(deductions) do   
            printSequent(deductions[i], file)
            if #deductions > 1 then
               file:write(" & ")
            end                 
         end

         file:write("\n}")
      end               
   end
end

local function printGoals(pos, goalsList)
   
   local seq,goal, sgoals

   for seq,goal in pairs(goalsList) do          
      if goal.rightGoals ~= nil then 
         for _,sgoals in pairs(goal.rightGoals) do 
            createDebugMessage(" ===>"..sgoals:getLabel())
         end
      end

      if goal.leftGoals ~= nil then 
         for _,sgoals in pairs(goal.leftGoals) do 
            createDebugMessage(" ===>"..sgoals:getLabel())
         end
      end
   end
end

-- Public functions


--- Create a graph from a formula in text form.
--- Returns a graph that represents the given formula.
--- @param formulaText - Formula in string form.
function LogicModule.createGraphFromTable( seq_tabela )
   local graph, goalsList
   local letters = {}

   if seq_tabela=="empty" then 
      graph = createGraphEmpty()
      return graph
   else
      graph, goalsList = createGraphSequent(seq_tabela, letters)
      return graph,goalsList
   end
end

--- Expand a operator in a sequent.
--- For a specific graph and a node of that graph, it expands the node if that node is an operator.
--- The operator node is only expanded if a sequent node were previusly selected.
--- @param graph The graph that contains the target node.
--- @param targetNode The node that you want to expand.
function LogicModule.expandNode( graph, GoalSequentNode,targetNode)
   assert( getmetatable(targetNode) == Node_Metatable , "expandNode expects a Node") -- Garantir que é um vertice

   local typeOfNode = targetNode:getInformation("type")
   local wasExpanded = true

   local newGraph = graph

   if not GoalSequentNode:getInformation("isExpanded") then
      if typeOfNode == opImp.graph then                 
         newGraph = expandNodeImp(graph, GoalSequentNode, targetNode)
         printGoals("1",goalsList)      
      else
         wasExpanded, newGraph = expandNodeAtomic(graph, GoalSequentNode, targetNode)
      end
   end


   if GoalSequentNode:getInformation("isExpanded") == false and wasExpanded then
      GoalSequentNode:setInformation("isExpanded", true)

      goalsList[GoalSequentNode:getLabel()]:deleteGoal() -- Ja usei esse sequente, nao guardo a lista de goals dele

      GoalSequentNode = nil -- Ja expandiu, agora escolhe um sequente de novo.
      createDebugMessage("Atualizou grafo!")            
   end

   return wasExpanded, newGraph
end

function LogicModule.expandAll(graph, goalsList)

   local newGraph = graph               
   local isAllExpanded = true
   local ret

   logger:debug("trace -- Starting ExpandAll...")
   for k,goal in pairs(goalsList) do -- 
      local seq = goal:getSequent()

      assert( getmetatable(seq) == Node_Metatable , "LogicModule.expandAll expects a Node")

      if not seq:getInformation("isExpanded") then
         isAllExpanded = false

         logger:debug("trace -- Expanding sequent "..k)

         local formulaNode = nil                        
         local leftSide = goal:getLeftSide()
         local rightSide = goal:getRightSide()

         if #rightSide ~= 0 then
            for k,formulaNode in pairs(rightSide) do 
               ret, newGraph = LogicModule.expandNode(graph, seq, formulaNode)
               if ret then break end
            end                                 
            if #leftSide ~= 0 then
               for k,formulaNode in pairs(leftSide) do 
                  ret, newGraph = LogicModule.expandNode(graph, seq, formulaNode)
                  if ret then break end
               end
            end
         else
            if #leftSide ~= 0 then
               for k,formulaNode in pairs(leftSide) do 
                  ret, newGraph = LogicModule.expandNode(graph, seq, formulaNode)
                  if ret then break end
               end
            end         
         end

         seq:setInformation("isExpanded", true)
         break
      end
   end

   if not isAllExpanded then
      ret, newGraph = LogicModule.expandAll(newGraph, goalsList)
   else
      local initialSequents = newGraph:getNode(lblNodeGG):getEdgesOut()

      if initialSequents ~= nil then
         for i=1, #initialSequents do
            markProvedSequent(initialSequents[i]:getDestino())
         end
      end
   end

   return ret, newGraph 
end

function LogicModule.printProof(graph)
   assert( getmetatable(graph) == Graph_Metatable , "printProof expects a graph.")      

   local file = io.open("aux/proof.tex", "w")   
   local goalEdge = graph:getNode(lblNodeGG):getEdgesOut()

   file:write("\\documentclass[landscape]{article}\n\n")

   file:write("\\usepackage{proof}\n")
   file:write("\\usepackage{qtree}\n\n")
   file:write("\\begin{document}\n")
   file:write("$$\n")

   if goalEdge ~= nil then
      local seq = goalEdge[1]:getDestino()
      printSequent(seq, file)
   end

   serializedSequent = serializedSequent:gsub("\\vdash", "⊨")
   serializedSequent = serializedSequent:gsub("\\to", "→")
   logger:info("statistics -- Serialized sequent: "..serializedSequent)  
   logger:info("statistics -- Size of serialized sequent: "..serializedSequent:len())  

   countGraphElements(graph)

   file:write("\n$$")   
   file:write("\\end{document}\n")
   file:close()
end

function LogicModule.expandNodeImpLeft(graph, sequentNode, nodeOpImp)

   local NewSequentNode1, seqListNodes1, seqListEdges1=createNewSequent(graph, sequentNode)
   local NewSequentNode2, seqListNodes2, seqListEdges2=createNewSequent(graph, sequentNode)
   graph:addNodes(seqListNodes1)
   graph:addNodes(seqListNodes2)
   graph:addEdges(seqListEdges1)
   graph:addEdges(seqListEdges2)
   local nodeRight1 = NewSequentNode1:getEdgeOut(lblEdgeDir):getDestino()
   local nodeLeft1 = NewSequentNode1:getEdgeOut(lblEdgeEsq):getDestino()
   local nodeRight2 = NewSequentNode2:getEdgeOut(lblEdgeDir):getDestino()
   local nodeLeft2 = NewSequentNode2:getEdgeOut(lblEdgeEsq):getDestino()

   local newEdge1 = SequentEdge:new(lblEdgeDeducao, sequentNode, NewSequentNode1)
   local newEdge2 = SequentEdge:new(lblEdgeDeducao, sequentNode, NewSequentNode2)
   graph:addEdge(newEdge1)
   graph:addEdge(newEdge2)

   -- Updating left (1) premiss of impLeft application
   
   --  First step: Deleting the expanded formula (nodeOpImp) from left side 
   -- local listEdgesOut = nodeLeft1:getEdgesOut() -- 
   -- for i=1, #listEdgesOut do
   --    if listEdgesOut[i]:getDestino():getLabel() == nodeOpImp:getLabel() then
   --       graph:removeEdge(listEdgesOut[i])
   --       break
   --    end
   -- end

   --Second step: Put formula outside brackets, inside. A new bracket is created
   -- to indicate de new stage of proof

   -- Remove edges from brackets. They will be recreated. 
   local nodeFormulaOutsideBrackets = nodeRight1:getEdgeOut("0"):getDestino() 
   graph:removeEdge(nodeRight1:getEdgeOut("0"))

   local newNodeBrackets = SequentNode:new(lblNodeBrackets)
   graph:addNode(newNodeBrackets)

   local numberFormulasInBrackets = 0  
   if nodeRight1:getEdgeOut("1") ~= nil then
      local oldNodeBrackets = nodeRight1:getEdgeOut("1"):getDestino()
      local copiedEdgeInsideBrackets = nil
      
      local listEdgesOut = oldNodeBrackets:getEdgesOut()
      for i=1, #listEdgesOut do
         copiedEdgeInsideBrackets = SequentEdge:new(""..i, newNodeBrackets, listEdgesOut[i]:getDestino())
         graph:addEdge(copiedEdgeInsideBrackets)
      end
      numberFormulasInBrackets = #oldNodeBrackets:getEdgesOut()
      graph:removeEdge(nodeRight1:getEdgeOut("1"))
   end
   
   local newEdgeInsideBrackets = SequentEdge:new(""..numberFormulasInBrackets, newNodeBrackets, nodeFormulaOutsideBrackets)
   graph:addEdge(newEdgeInsideBrackets)

   local newBracketsEdge = SequentEdge:new("1", nodeRight1, newNodeBrackets)
   graph:addEdge(newBracketsEdge)


   -- Third step: updating the right side of the sequent as the antecedent of the nodeOpImp formula
   local newEdgeDir = SequentEdge:new("0", nodeRight1, nodeOpImp:getEdgeOut(lblEdgeEsq):getDestino())   
   graph:addEdge(newEdgeDir)
   -- End of updating left (1) premiss

   -- Updating right (2) premiss of impLeft application

   -- First step: updating the left side of the sequent (premiss 2)  
   local listEdgesOut = nodeLeft2:getEdgesOut()
   for i=1, #listEdgesOut do
      if listEdgesOut[i]:getDestino():getLabel() == nodeOpImp:getLabel() then
         local labelEdgeRemoved = listEdgesOut[i]:getLabel()
         graph:removeEdge(listEdgesOut[i])
         break
      end
   end

   -- Second step:
   local newEdgeLeft = SequentEdge:new(labelEdgeRemoved, nodeLeft2, nodeOpImp:getEdgeOut(lblEdgeDir):getDestino()) 
   graph:addEdge(newEdgeLeft)

   -- End of updating right (2) premiss

   goalsList[NewSequentNode1:getLabel()] = GoalsLogic.assembleGoalList(NewSequentNode1)
   goalsList[NewSequentNode2:getLabel()] = GoalsLogic.assembleGoalList(NewSequentNode2)

   return graph, goalsList      
end

function LogicModule.expandNodeImpRight(graph, sequentNode, nodeOpImp)
   local NewSequentNode, seqListNodes, seqListEdges=createNewSequent(graph, sequentNode)

   graph:addNodes(seqListNodes)
   graph:addEdges(seqListEdges)
   local nodeRight = NewSequentNode:getEdgeOut(lblEdgeDir):getDestino()
   local nodeLeft = NewSequentNode:getEdgeOut(lblEdgeEsq):getDestino()
   local newEdge1 = SequentEdge:new(lblEdgeDeducao, sequentNode, NewSequentNode)
   graph:addEdge(newEdge1)      

   local listEdgesOut = nodeRight:getEdgesOut()
   for i=1, #listEdgesOut do
      if listEdgesOut[i]:getDestino():getLabel() == nodeOpImp:getLabel() then
         labelEdgeRemoved = listEdgesOut[i]:getLabel()
         graph:removeEdge(listEdgesOut[i])
         break
      end
   end
   local newEdge2 = SequentEdge:new(labelEdgeRemoved, nodeRight, nodeOpImp:getEdgeOut(lblEdgeDir):getDestino())

   local numberEdgesLeft = #nodeLeft:getEdgesOut()
   local newEdge3 = SequentEdge:new(""..numberEdgesLeft, nodeLeft, nodeOpImp:getEdgeOut(lblEdgeEsq):getDestino())

   graph:addEdge(newEdge2)
   graph:addEdge(newEdge3)        

   goalsList[NewSequentNode:getLabel()] = GoalsLogic.assembleGoalList(NewSequentNode)

   return graph, goalsList      
end

--- Verifies operator side in a sequent
--- Return "Left" if the operatorNode is in the left side of the sequentNode
--- Return "Right" if the operatorNode is in the right side of the sequentNode
--- Return "Left" if the operatorNode is in the left side of the sequentNode
--- @param sequentNode a node that the operatorNode should participate
--- @param operatorNode a node that is the logical constant focused
function LogicModule.verifySideOfOperator(sequentNode, operatorNode)
   assert( operatorNode ~= nil , "verifySideOfOperator must be called only if operatorNode is not null.")
   assert( getmetatable(operatorNode) == Node_Metatable , "verifySideOfOperator operatorNode must be a Node")
   assert( sequentNode ~= nil , "verifySideOfOperator must be called only if sequentNode is not null.") 
   assert( getmetatable(sequentNode) == Node_Metatable , "verifySideOfOperator sequentNode must be a Node")

   seqEdgesOutList = sequentNode:getEdgesOut()
   if seqEdgesOutList == nil then
      return nil
   end

   for i=1, #seqEdgesOutList do
      if seqEdgesOutList[i]:getLabel() == lblEdgeEsq then
         if verifySideOfSequent(seqEdgesOutList[i]:getDestino(), operatorNode) then
            return "Left"
         end
      end

      if seqEdgesOutList[i]:getLabel() == lblEdgeDir then
         if verifySideOfSequent(seqEdgesOutList[i]:getDestino(), operatorNode) then
            return "Right"
         end
      end               
   end
   
   return nil 
end
