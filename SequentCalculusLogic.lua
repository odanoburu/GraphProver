-------------------------------------------------------------------------------
--   Sequent Calculus Module
--
--   This module defines the ...
--
--   @authors: Vitor, Bruno, Hermann, Jefferson
--
-------------------------------------------------------------------------------

require "SequentGraph"
require "Goal"
require "ConstantsForSequent"
require "logging" 
require "logging.file"

local logger = logging.file("aux/prover-SequentCalculus%s.log", "%Y-%m-%d")
logger:setLevel(logging.DEBUG)

LogicModule = {}

local goalsList = nil
local graph = nil
local counterModel = nil
local serializedSequent = ""
local foundNodes = {}

-- Private functions

local function createNewSequent(sequentNode)
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

local function assembleGoalList(sequentNode)

   if goalsList == nil then
      goalsList = {}
   end
   
   assert( getmetatable(sequentNode) == Node_Metatable, "assembleGoalList: sequentNode must not be a node.")
   
   local newGoal = nil  

   local esqNode = sequentNode:getEdgeOut(lblEdgeEsq):getDestino()
   local dirNode = sequentNode:getEdgeOut(lblEdgeDir):getDestino()

   local j = 1
   
   local leftGoals = {}
   local esqEdges = esqNode:getEdgesOut()
   
   if esqEdges ~= nil then
      for i=1, #esqEdges do
         local nodeEsq = esqEdges[i]:getDestino()
         local typeOfNode = nodeEsq:getInformation("type")

         if typeOfNode == opImp.graph then
            leftGoals[j] = nodeEsq
            j = j + 1
         end
      end
   end  
   j = 1
   local rightGoals = {}
   local dirEdges = dirNode:getEdgesOut()
   if dirEdges ~= nil then 
      for i=1, #dirEdges do
         local nodeDir = dirEdges[i]:getDestino()
         local typeOfNode = nodeDir:getInformation("type")

         if typeOfNode == opImp.graph then
            rightGoals[j] = nodeDir
            j = j + 1
         end
      end
   end
   newGoal = Goal:new (sequentNode, leftGoals, rightGoals)
                
   return newGoal
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

      NodeLetter:setInformation("copiedCount", 0)
         
      nodes={NodeLetter}
      edges={}
      
      FormulaGraph:addNodes(nodes)
      FormulaGraph:addEdges(edges)
      FormulaGraph:setRoot(NodeLetter)
      
   elseif formula_tabela.tag == "imp" then

      S1,letters= createGraphFormula(formula_tabela["1"],letters)
      S2,letters = createGraphFormula(formula_tabela["2"],letters)

      local NodeImp = SequentNode:new(opImp.graph)
      local EdgeEsq = SequentEdge:new(lblEdgeEsq, NodeImp, S1.root)
      local EdgeDir = SequentEdge:new(lblEdgeDir, NodeImp, S2.root)

      NodeImp:setInformation("copiedCount", 0)      

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

   local SequentGraph = Graph:new ()
   local S,L
   local NodeGG = SequentNode:new(lblNodeGG)
   local NodeSeq = SequentNode:new(opSeq.graph)
   local NodeEsq = SequentNode:new(lblNodeEsq)
   local NodeDir = SequentNode:new(lblNodeDir)
   local NodeBrackets = SequentNode:new(lblNodeBrackets)
   local NodeFocus = SequentNode:new(lblNodeFocus)
   S,L = createGraphFormula(seq_tabela, letters)

   local Edge1 = SequentEdge:new(lblEdgeGoal, NodeGG, NodeSeq)
   local Edge2 = SequentEdge:new(lblEdgeEsq, NodeSeq, NodeEsq)
   local Edge3 = SequentEdge:new(lblEdgeDir, NodeSeq, NodeDir)
   local Edge4 = SequentEdge:new('', NodeDir, S.root)
   local Edge5 = SequentEdge:new('', NodeDir, NodeBrackets)
   local Edge6 = SequentEdge:new('', NodeEsq, NodeFocus)

   local nodes = {NodeGG, NodeSeq, NodeDir, NodeEsq, NodeBrackets, NodeFocus}
   SequentGraph:addNodes(nodes)
   SequentGraph:addNodes(S.nodes)
   local edges = {Edge1, Edge2, Edge3, Edge4, Edge5, Edge6}    
   SequentGraph:addEdges(edges)
   SequentGraph:addEdges(S.edges)


   goalsList={}
   goalsList[NodeSeq:getLabel()] = assembleGoalList(NodeSeq)
   return SequentGraph
end

local function verifySideOfSequent(sequentNode, formulaNode)
   edgesOut = sequentNode:getEdgesOut()

   if edgesOut == nil then
      return false
   end

   local retValues = {}

   for i=1, #edgesOut do
      if edgesOut[i]:getDestino():getLabel() == formulaNode:getLabel() then
         return true
      end
   end

   return false
end

--- Verifies operator side in a sequent
local function verifySideOfOperator(sequentNode, formulaNode)
   assert( sequentNode ~= nil , "verifySideOfOperator must be called only if sequentNode is not null.")
   assert( getmetatable(sequentNode) == Node_Metatable , "verifySideOfOperator sequentNode must be a Node")
   assert( formulaNode ~= nil , "verifySideOfOperator must be called only if formulaNode is not null.") 
   assert( getmetatable(formulaNode) == Node_Metatable , "verifySideOfOperator formulaNode must be a Node")

   seqEdgesOutList = sequentNode:getEdgesOut()
   if seqEdgesOutList == nil then
      return nil
   end

   for i=1, #seqEdgesOutList do
      if seqEdgesOutList[i]:getLabel() == lblEdgeEsq then
         if verifySideOfSequent(seqEdgesOutList[i]:getDestino(), formulaNode) then
            return "Left"
         end
      end

      if seqEdgesOutList[i]:getLabel() == lblEdgeDir then
         if verifySideOfSequent(seqEdgesOutList[i]:getDestino(), formulaNode) then
            return "Right"
         end
      end               
   end
   
   return nil 
end

local function markProvedPath(sequentNode) 
   local seq = sequentNode

   while seq ~= nil do
      seq:setInformation("isProved", true)
      if seq:getEdgeIn(lblEdgeDeducao) then 
        seq = seq:getEdgeIn(lblEdgeDeducao):getOrigem()
      else
        seq = nil
      end
   end
end

local function markCounterExamplePath(sequentNode) 
   local seq = sequentNode

   while seq ~= nil do
      seq:setInformation("isProved", false)
      if seq:getEdgeIn(lblEdgeDeducao) then 
        seq = seq:getEdgeIn(lblEdgeDeducao):getOrigem()
      else
        seq = nil
      end
   end
end

local function countGraphElements() 
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
      logger:info("statistics -- Total nodes of type "..krgrep.." is "..count)
   end

   for k,count in pairs(countEdgesElements) do
      logger:info("statistics -- Total nodes of type "..k.." is "..count)
   end

end

local function printFormula(formulaNode)
   local ret = ""
   local edge, subformula = nil

   local formulaNumber = formulaNode:getLabel():sub(6,formulaNode:getLabel():len())

   if (formulaNode:getEdgesOut() ~= nil) and (#formulaNode:getEdgesOut() ~= 0) then
      if formulaNode:getLabel():sub(1,2) == lblNodeBrackets then
         ret = ret.."["
         for i, edge in ipairs(formulaNode:getEdgesOut()) do
            subformula = edge:getDestino()
            ret = ret..printFormula(subformula)..","
         end
         ret = ret:sub(1, ret:len()-1)
         ret = ret.."]"
      else
         for i, edge in ipairs(formulaNode:getEdgesOut()) do
            if edge:getLabel() == lblEdgeEsq then
               subformula = edge:getDestino()
               ret = ret.."("..printFormula(subformula)
            end
         end    

         ret = ret.." "..opImp.tex.."_{"..formulaNumber.."} "

         for i, edge in ipairs(formulaNode:getEdgesOut()) do
            if edge:getLabel() == lblEdgeDir then
               subformula = edge:getDestino()
               ret = ret..printFormula(subformula)..")"
            end
         end    
      end
   else
      ret = formulaNode:getLabel()
      if formulaNode:getLabel():sub(1,2) == lblNodeBrackets then
         ret = ret:sub(1, ret:len()-1)
      end
   end

   return ret

end

local function printSequent(sequentNode, file)
   local ret = ""
   local edge, nodeEsq, nodeDir = nil
   local deductions = {}
   local j = 1

   if sequentNode ~= nil then

      local seqNumber = sequentNode:getLabel():sub(4,sequentNode:getLabel():len())
      
      for i, edge in ipairs(sequentNode:getEdgesOut()) do       
         if edge:getLabel() == lblEdgeEsq then
            nodeEsq = edge:getDestino()
         end
         if edge:getLabel() == lblEdgeDir then
            nodeDir = edge:getDestino()
         end
         if edge:getLabel() == lblEdgeDeducao then
            sequentNode = edge:getDestino()
            deductions[j] = sequentNode
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

      ret = ret.." "..opSeq.tex.."_{"..seqNumber.."} "

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

local function compareFormulasUsage(formulaA, formulaB)
  
   local countFormulaA, countFormulaB

   countFormulaA = formulaA:getInformation("copiedCount")
   countFormulaB = formulaB:getInformation("copiedCount")   

   if formulaA == nil or formulaA:getInformation("copiedCount") == nil then
      countFormulaA = 0
   end

   if formulaB == nil or formulaB:getInformation("copiedCount") == nil then
      countFormulaB = 0
   end

   return countFormulaB > countFormulaA --to force alternating formulae with same count 
end

local function compareSideFormulas(sideSeq, sideSeqParent)

   local edgeSeqParent
   local formulaSeq
   local formulasSeqParent = {}
   local ret = true
   local i = 0   

   for _, edgeSeqParent in ipairs(sideSeqParent:getEdgesOut()) do
      if edgeSeqParent:getDestino():getInformation("type") ~= lblNodeBrackets then
         i = i + 1
         formulasSeqParent[i] = edgeSeqParent:getDestino()
      end      
   end

   local setOfFormulas = Set:new(formulasSeqParent)

   for _, edgeSeq in ipairs(sideSeq:getEdgesOut()) do
      formulaSeq = edgeSeq:getDestino()
      if formulaSeq:getInformation("type") ~= lblNodeBrackets then
         if not setOfFormulas:contains(formulaSeq) then
            ret = false
            break
         end
      end
   end

   return ret
end

local function compareBracketFormulas(sideSeq, sideSeqParent)
  
   local edgeSeqParent
   local formulaSeq
   local formulasSeqParent = {}
   local ret = true
   local i = 0   

   for _, edgeSeqParent in ipairs(sideSeqParent:getEdgeOut(lblEdgeDir):getDestino("1"):getEdgesOut()) do
      i = i + 1
      formulasSeqParent[i] = edgeSeqParent:getDestino()
   end

   local setOfFormulas = Set:new(formulasSeqParent)

   for _, edgeSeq in ipairs(sideSeq:getEdgeOut(lblEdgeDir):getDestino("1"):getEdgesOut()) do
      formulaSeq = edgeSeq:getDestino()
      if not setOfFormulas:contains(formulaSeq) then
         ret = false
         break
      end
   end

   return ret
end

local function verifyLoopCondition(sequentNode)
   local ret = true

   if sequentNode:getEdgeOut(lblEdgeEsq) ~= nil then
      local leftFormulasEdges = sequentNode:getEdgeOut(lblEdgeEsq):getDestino():getEdgesOut()
      
      for i=1, #leftFormulasEdges do
         local formulaNode = leftFormulasEdges[i]:getDestino()
         local typeOfNode = formulaNode:getInformation("type")
         if typeOfNode == opImp.graph and formulaNode:getInformation("copiedCount") == 0 then
            ret = false
         end
      end
   end
      
   if ret then
      local rightFormulaNode = sequentNode:getEdgeOut(lblEdgeDir):getDestino():getEdgeOut("0")
      local typeOfNode = rightFormulaNode:getInformation("type")   
      if typeOfNode == opImp.graph then
         ret = false
      end
   end
   
   return ret
end

local function checkLoop(sequentNode)
  
   local esqNode, dirNode, dedSeq, esqNodeAnt, dirNodeAnt
   local ret = false
   local equalLeft, equalRight, equalBracket
   
   esqNode = sequentNode:getEdgeOut(lblEdgeEsq):getDestino()
   dirNode = sequentNode:getEdgeOut(lblEdgeDir):getDestino()

   dedSeq = sequentNode:getEdgeIn(lblEdgeDeducao):getOrigem()

   while dedSeq ~= nil do     
      esqNodeAnt = dedSeq:getEdgeOut(lblEdgeEsq):getDestino()
      dirNodeAnt = dedSeq:getEdgeOut(lblEdgeDir):getDestino()

      equalLeft = compareSideFormulas(esqNode, esqNodeAnt)      
      equalRight = compareSideFormulas(dirNode, dirNodeAnt)
      equalBracket = compareBracketFormulas(sequentNode, dedSeq)
      
      if equalLeft and equalRight and equalBracket then
         ret = true
         markCounterExamplePath(dedSeq)
         break
      else
         if dedSeq:getEdgeIn(lblEdgeDeducao) == nil then
            dedSeq = nil
         else
            dedSeq = dedSeq:getEdgeIn(lblEdgeDeducao):getOrigem()
         end
      end
   end

   return ret
end

local function generateCounterModel(sequentNode, counterModel)

  local ret = nil

   if counterModel == nil then

      -- Cria nós dos mundos
      local world0 = Node:new(lblNodeWorld.."0")
      world0:setInformation("type", lblNodeWorld)
      
      local world1 = Node:new(lblNodeWorld.."1")
      world1:setInformation("type", lblNodeWorld)

      -- Criar aresta do sequente para o mundo 0
      local edgeCounter = Edge:new(lblEdgeCounterModel, sequentNode, world0)
      
      -- Criar aresta do mundo 0 para o mundo 1
      local edgeAccess = Edge:new(lblEdgeAccessability, world0, world1)

      -- Adicionar nós e arestas no grafo
      graph:addNode(world0)
      graph:addNode(world1)
      graph:addEdge(edgeCounter)
      graph:addEdge(edgeAccess)
      
      local seqSideRight = sequentNode:getEdgeOut(lblEdgeDir):getDestino()
      local seqSideLeft = sequentNode:getEdgeOut(lblEdgeEsq):getDestino()
      local formula = nil
      local edgeSat = nil

      -- Para cada formula à esq do sequente, criar aresta SAT ligando ao mundo 1
      local leftFormulasEdges = seqSideLeft:getEdgesOut()
      for i=1,#leftFormulasEdges do
         formula = leftFormulasEdges[i]:getDestino()
         edgeSat = Edge:new(lblEdgeSatisfy, world1, formula)
         graph:addEdge(edgeSat)
      end

      -- Para cada formula à direita:
      -- Se estiver fora do bracket criar aresta NOT SAT ligando ao mundo 1
      local formulaOutsideBracket = seqSideRight:getEdgeOut("0"):getDestino()
      edgeSat = Edge:new(lblEdgeSatisfy, world1, formula)
      graph:addEdge(edgeSat)

      -- Se estiver no bracket criar aresta NOT SAT ligando ao mundo 0      
      local formulasInsideBracketEdges = seqSideRight:getEdgeOut("1"):getDestino():getEdgesOut()      
      for i=1,#formulasInsideBracketEdges do
         formula = formulasInsideBracketEdges[i]:getDestino()
         edgeSat = Edge:new(lblEdgeUnsatisfy, world0, formula)
         graph:addEdge(edgeSat)
      end
      
      ret = world0      
      
   end
   
   return ret3

end

local function getInitialSequent()
   if graph then  
      local goalEdge = graph:getNode(lblNodeGG):getEdgeOut(lblEdgeGoal)
      
      if goalEdge then
        return goalEdge:getDestino()
      end
   end
end

local function verifyAxiom(sequentNode)
   local edgesLeft = sequentNode:getEdgeOut(lblEdgeEsq):getDestino():getEdgesOut()
   local rightFormulaNode = sequentNode:getEdgeOut(lblEdgeDir):getDestino():getEdgeOut("0"):getDestino()
   local side = " "
   local isAxiom = false

   for i=1, #edgesLeft do
      if edgesLeft[i]:getDestino():getInformation("type") ~= opImp.graph and
         rightFormulaNode:getInformation("type") ~= opImp.graph then
         if edgesLeft[i]:getDestino():getLabel() == rightFormulaNode:getLabel() then
            isAxiom = true
            break
         end
      end
   end 

   if isAxiom then
      sequentNode:setInformation("isAxiom", true)
      sequentNode:setInformation("isExpanded", true)
      logger:info("verifyAxiom - "..sequentNode:getLabel().." is axiom")
      logger:info("verifyAxiom - "..sequentNode:getLabel().." was expanded")

      markProvedPath(sequentNode)     
      return true 
   else   
      return false
   end
end

local function putFormulaInFcus(sequentNode, formulaNode)
   local newSequentNode = createNewSequent(sequentNode)

end

local function expandNodeImpLeft(sequentNode, formulaNode)
   logger:debug("expandNodeImpLeft: Expanding sequent "..sequentNode:getLabel().. " and formula "..formulaNode:getLabel())
   
   local NewSequentNode1, seqListNodes1, seqListEdges1=createNewSequent(sequentNode)
   local NewSequentNode2, seqListNodes2, seqListEdges2=createNewSequent(sequentNode)
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

   -- 1. Create left premiss sequent:

   -- 1.0. Leave A \to B on the left, but mark it as used
   local listEdgesOut = nodeLeft1:getEdgesOut() --
   for i=1, #listEdgesOut do
      if listEdgesOut[i]:getDestino():getLabel() == formulaNode:getLabel() then
         copiedCount = listEdgesOut[i]:getDestino():getInformation("copiedCount")
         copiedCount = copiedCount + 1
         listEdgesOut[i]:getDestino():setInformation("copiedCount", copiedCount)
         break
      end
   end
   
   -- 1.1. Put C inside bracket. We have to create a new bracket to not loose the proof's history on graph.
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

   -- 1.2. Put A (from A \to B) on the right.
   local newEdgeDir = SequentEdge:new("0", nodeRight1, formulaNode:getEdgeOut(lblEdgeEsq):getDestino())   
   graph:addEdge(newEdgeDir)

   
   -- 2. Create right premiss sequent:
   
   -- 2.1. Remove A \to B from the left  
   local listEdgesOut = nodeLeft2:getEdgesOut()
   for i=1, #listEdgesOut do
      if listEdgesOut[i]:getDestino():getLabel() == formulaNode:getLabel() then
         copiedCount = listEdgesOut[i]:getDestino():getInformation("copiedCount")
         copiedCount = copiedCount + 1
         listEdgesOut[i]:getDestino():setInformation("copiedCount", copiedCount)
         break
      end
   end   

   -- 2.2. Add B (from A \to B) on the left
   local newEdgeLeft = SequentEdge:new(labelEdgeRemoved, nodeLeft2, formulaNode:getEdgeOut(lblEdgeDir):getDestino()) 
   graph:addEdge(newEdgeLeft)
   
   -- Add left and right premisses as new sequent goals
   local loopcheck1, loopcheck2 = false, false
   if verifyLoopCondition(NewSequentNode1) then
      loopcheck1 = checkLoop(NewSequentNode1)
   end
   if verifyLoopCondition(NewSequentNode2) then
      loopcheck2 = checkLoop(NewSequentNode2)
   end
   
   if not loopcheck1 and not loopcheck2 then
      if not verifyAxiom(NewSequentNode1) then
         goalsList[NewSequentNode1:getLabel()] = assembleGoalList(NewSequentNode1)
      end

      if not verifyAxiom(NewSequentNode2) then
         goalsList[NewSequentNode2:getLabel()] = assembleGoalList(NewSequentNode2)
      end
   else
      if loopcheck1 then 
         logger:info("expandNodeImpLeft - check in loop found on "..NewSequentNode1:getLabel().."!!!")
         counterModel = generateCounterModel(NewSequentNode1, counterModel)
      else
         logger:info("expandNodeImpLeft - check in loop found on "..NewSequentNode2:getLabel().."!!!")
         counterModel = generateCounterModel(NewSequentNode2, counterModel)
      end
      goalsList = {}
   end
     
   return graph      
end

local function expandNodeImpRight(sequentNode, formulaNode)
   logger:debug("expandNodeImpRight: Expanding sequent "..sequentNode:getLabel().. " and formula "..formulaNode:getLabel())
   
   local NewSequentNode, seqListNodes, seqListEdges=createNewSequent(sequentNode)

   graph:addNodes(seqListNodes)
   graph:addEdges(seqListEdges)
   local nodeRight = NewSequentNode:getEdgeOut(lblEdgeDir):getDestino()
   local nodeLeft = NewSequentNode:getEdgeOut(lblEdgeEsq):getDestino()
   local newEdge1 = SequentEdge:new(lblEdgeDeducao, sequentNode, NewSequentNode)
   graph:addEdge(newEdge1)      

   local listEdgesOut = nodeRight:getEdgesOut()
   for i=1, #listEdgesOut do
      if listEdgesOut[i]:getDestino():getLabel() == formulaNode:getLabel() then
         labelEdgeRemoved = listEdgesOut[i]:getLabel()
         graph:removeEdge(listEdgesOut[i])
         break
      end
   end
   local newEdge2 = SequentEdge:new(labelEdgeRemoved, nodeRight, formulaNode:getEdgeOut(lblEdgeDir):getDestino())

   local numberEdgesLeft = #nodeLeft:getEdgesOut()
   local newEdge3 = SequentEdge:new(""..numberEdgesLeft, nodeLeft, formulaNode:getEdgeOut(lblEdgeEsq):getDestino())

   graph:addEdge(newEdge2)
   graph:addEdge(newEdge3)

   local loopcheck = false
   if verifyLoopCondition(NewSequentNode) then
      loopcheck = checkLoop(NewSequentNode)
   end   

   if not loopcheck then
      if not verifyAxiom(NewSequentNode) then
         goalsList[NewSequentNode:getLabel()] = assembleGoalList(NewSequentNode)
      end
   else
      logger:info("expandNodeImpRight - check in loop found on "..NewSequentNode:getLabel().."!!!")
      counterModel = generateCounterModel(NewSequentNode, counterModel)
      goalsList = {}
   end

   return graph     
end

local function expandNodeImp(sequentNode, formulaNode)

   local sideOfOperator = verifySideOfOperator(sequentNode, formulaNode)      

   if sideOfOperator == leftSide then
      return expandNodeImpLeft(sequentNode, formulaNode)
   elseif sideOfOperator == rightSide then
      return expandNodeImpRight(sequentNode, formulaNode)
   elseif sideOfOperator == nil then
      return nil
   end          

   return graph
end

-- Public functions

--- Create a graph from a formula in text form.
--- Returns a graph that represents the given formula.
--- @param seq_tabela - Formula in table form.
function LogicModule.createGraphFromTable(seq_tabela)
   local letters = {}

   if seq_tabela=="empty" then 
      graph = createGraphEmpty()
      return graph
   else
      graph = createGraphSequent(seq_tabela, letters)
      return graph
   end
end

--- Expand a operator in a sequent.
--- For a specific graph and a node of that graph, it expands the node if that node is an operator.
--- The operator node is only expanded if a sequent node were previusly selected.
--- @param agraph 
--- @param sequentNode  
--- @param formulaNode 
function LogicModule.expandNode(agraph, sequentNode, formulaNode)
   assert(getmetatable(formulaNode) == Node_Metatable , "expandNode expects a Node") -- Garantir que é um vertice

   local typeOfNode = formulaNode:getInformation("type")

   graph = agraph

   if not sequentNode:getInformation("isExpanded") then
      if typeOfNode == opImp.graph then                 
         graph = expandNodeImp(sequentNode, formulaNode)  
      end
   end

   return true, graph      
end

function LogicModule.expandAll(agraph)

   local isAllExpanded = true
   local ret
   local k, goal 
   local last_kx

   graph = agraph               
   
   for k,goal in pairs(goalsList) do
      last_k = k
      local seq = goal:getSequent()

      assert( getmetatable(seq) == Node_Metatable , "LogicModule.expandAll expects a Node")

      if not seq:getInformation("isExpanded") then
         isAllExpanded = false

         local formulaNode = nil                        
         local leftSide = goal:getLeftSide()
         local rightSide = goal:getRightSide()

         table.sort(leftSide, compareFormulasUsage)
         table.sort(rightSide, compareFormulasUsage)         

         if #rightSide ~= 0 then
            for _,formulaNode in pairs(rightSide) do
               ret, graph = LogicModule.expandNode(graph, seq, formulaNode)
               LogicModule.printProof(graph, k)
            end
         else
            if #leftSide ~= 0  then
               for _,formulaNode in pairs(leftSide) do
                  ret, graph = LogicModule.expandNode(graph, seq, formulaNode)
                  LogicModule.printProof(graph, k)                  
                  break
               end
            end
         end

         seq:setInformation("isExpanded", true)
         logger:info("expandAll - "..k.." was expanded")        
         break
      end
   end

   if not isAllExpanded then
      ret, graph = LogicModule.expandAll(graph)
   else
     logger:info("expandAll - All sequents expanded after sequent")
   end

   return ret, graph 
end

function LogicModule.printProof(agraph, nameSufix)
   assert( getmetatable(agraph) == Graph_Metatable , "printProof expects a graph.")

   graph = agraph

   if nameSufix == nil then nameSufix = "" end
   
   local file = io.open("aux/prooftree"..nameSufix..".tex", "w")   
   local goalEdge = agraph:getNode(lblNodeGG):getEdgesOut()
   local ret = false

   if (goalEdge ~= nil) and (#goalEdge > 0) then
      
      local seq = goalEdge[1]:getDestino()

      file:write("\\documentclass[landscape]{article}\n\n")
      file:write("\\usepackage{proof}\n")
      file:write("\\usepackage{qtree}\n\n")
      file:write("\\begin{document}\n")
      file:write("$$\n")

      printSequent(seq, file)
      
      serializedSequent = serializedSequent:gsub("\\vdash", "⊨")
      serializedSequent = serializedSequent:gsub("\\to", "→")
      --logger:info("statistics -- Serialized sequent: "..serializedSequent)  
      --logger:info("statistics -- Size of serialized sequent: "..serializedSequent:len())  
      --countGraphElements()

      file:write("\n$$")   
      file:write("\\end{document}\n")
      file:close()

      ret = true
   end

   return ret
end

function LogicModule.getGraph()
  return graph
end


-- API functions to interact from graphical interface
local function findf(seq, form, side)
   local seqNode = finds(seq)
   local ret = nil
   local formulaNode = nil
   
   if seqNode ~= nil then
      local listEdgesOut = seqNode:getEdgeOut(side):getDestino():getEdgesOut()
      for i=1,#listEdgesOut do
         formulaNode = listEdgesOut[i]:getDestino()
         if formulaNode:getLabel():lower() == form:lower() then
            ret = formulaNode
            break
         end
      end
   end

   return ret
end

function finds(seq)
   local goalEdge = graph:getNode(lblNodeGG):getEdgesOut()
   local seqNode = goalEdge[1]:getDestino()

   while seqNode ~= nil do
      if seqNode:getLabel():lower() == seq:lower() then
         seqNode:setInformation("found", true)
         table.insert(foundNodes, seqNode)
         
         local leftSide = seqNode:getEdgeOut(lblEdgeEsq):getDestino()
         local rightSide = seqNode:getEdgeOut(lblEdgeDir):getDestino()
         
         leftSide:setInformation("found", true)
         table.insert(foundNodes, leftSide)
         
         for i=1,#leftSide:getEdgesOut() do
            local formulaNode = leftSide:getEdgesOut()[i]:getDestino()
            formulaNode:setInformation("found", true)
            table.insert(foundNodes, formulaNode)
         end

         rightSide:setInformation("found", true)
         table.insert(foundNodes, rightSide)
         
         for i=1,#rightSide:getEdgesOut() do
            local formulaNode = rightSide:getEdgesOut()[i]:getDestino()
            formulaNode:setInformation("found", true)
            table.insert(foundNodes, formulaNode)
         end         
         break
      end

      seqNode = seqNode:getEdgeOut(lblEdgeDeducao):getDestino()
   end
   
   return seqNode
end

function clear()
   for i=1,#foundNodes do
      foundNodes[i]:setInformation("found", false)
   end
end

function load()
   local f=loadfile("commands.lua")
   f()
end

function ileft(seq, form)
   local seqNode = finds(seq)
   local formNode = findf(seq, form, "esq")

   graph = expandNodeImpLeft(seqNode, formNode)
   clear()
end

function iright(seq, form)
   local seqNode = finds(seq)
   local formNode = findf(seq, form, "dir")

   graph = expandNodeImpRight(seqNode, formNode)
   clear()
end
