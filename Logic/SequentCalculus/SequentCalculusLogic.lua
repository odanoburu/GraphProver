
-------------------------------------------------------------------------------
--   Sequent Calculus Module
--
--   This module defines the ...
--
--   @authors: Vitor, Bruno, Hermann, Jefferson
--
-------------------------------------------------------------------------------
require "Logic/SequentCalculus/SequentCalculusHelper"
require "Logic/SequentCalculus/SequentCalculusPrint"

local logger = logging.file("aux/prover%s.log", "%Y-%m-%d")
logger:setLevel(logging.INFO)

LogicModule = {}

local goalsList = nil
local graph = nil
local counterModel = nil
local contBracketFormulas = 0
local nstep = 0
local sufix = 0

-- Private functions

local function generateNewGoal(sequentNode)

   if goalsList == nil then
      goalsList = {}
   end

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
   SequentNode:resetCounters()

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
   local NodeLetter=nil
   local FormulaGraph = Graph:new ()
   --SequentNode:resetCounters()

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
   goalsList[NodeSeq:getLabel()] = {goal = generateNewGoal(NodeSeq), weight = 1}

   local focusedFormulas = Set:new()
   NodeSeq:setInformation("focusedFormulas", focusedFormulas)

   local leftExpandedFormulas = {}
   NodeSeq:setInformation("leftExpandedFormulas", leftExpandedFormulas)

   local restartedFormulas = Set:new()
   NodeSeq:setInformation("restartedFormulas", restartedFormulas)

   SequentGraph:setRoot(NodeGG)

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

local function logGoalsList()
   logger:info("GoalsList:")
   for k,v in pairs(goalsList) do
      if not goalsList[k].goal:getSequent():getInformation("isExpanded") then
         logger:info("seq: "..k.."; weight: "..goalsList[k].weight)
      end
   end
end

local function resetGoalsWeight(pweight)

   local k, goalEntry

   for k,goalEntry in pairs(goalsList) do
      goalEntry.weight = pweight
   end
end

local function degreeOfFormula(formulaNode)
   if formulaNode:getInformation("type") ~= opImp.graph then
      return 0
   else
      local degree = 1 + degreeOfFormula(formulaNode:getEdgeOut(lblEdgeDir):getDestino()) + degreeOfFormula(formulaNode:getEdgeOut(lblEdgeEsq):getDestino())
      return degree
   end
end

local function compareGoalsListWeight(goalEntryA, goalEntryB)

  return goalEntryB.weight > goalEntryA.weightA
end

local function compareFormulasDegree(formulaA, formulaB)

   local countFormulaA, countFormulaB

   countFormulaA = degreeOfFormula(formulaA)
   countFormulaB = degreeOfFormula(formulaB)

  return countFormulaB > countFormulaA
end

local function compareEdgesInBracket(edgeA, edgeB)

   local posA = tonumber(edgeA:getLabel())
   local posB = tonumber(edgeB:getLabel())

   return posA > posB

end

local function compareSequentsFormulas(sideSeq, sideSeqParent)

   local edgeSeqParent
   local formulaSeq
   local formulasSeqParent = {}
   local ret = true
   local i = 0

   if sideSeqParent:getEdgesOut() == nil then
      formulasSeqParent = {}
   else
      for _, edgeSeqParent in ipairs(sideSeqParent:getEdgesOut()) do
         if edgeSeqParent:getDestino():getInformation("type") ~= lblNodeFocus and
            edgeSeqParent:getDestino():getInformation("type") ~= lblNodeBrackets then

               local formulaNode = nil
               local ref = ""

               if edgeSeqParent:getDestino():getInformation("originalFormula") ~= nil then
                  formulaNode = edgeSeqParent:getDestino():getInformation("originalFormula")
                  local leftNodeParent = sideSeqParent:getEdgeIn("0"):getDestino()
                  for _, edgeLeftParent in ipairs(leftNodeParent:getEdgesOut()) do
                     if edgeLeftParent:getDestino() == formulaNode then
                        ref = edgeLeftParent:getInformation("reference"):getLabel()
                     end
                  end
               else
                  formulaNode = edgeSeqParent:getDestino()
                  if edgeSeqParent:getInformation("reference") ~= nil then
                     ref = edgeSeqParent:getInformation("reference"):getLabel()
                  end
               end

               i = i + 1
               formulasSeqParent[i] = formulaNode:getLabel()..ref
         end
      end
   end

   if sideSeq:getEdgesOut() == nil then
      if formulasSeqParent == nil then
         ret = true
      else
         ret = false
      end
   else
      local setOfFormulas = Set:new(formulasSeqParent)

      for _, edgeSeq in ipairs(sideSeq:getEdgesOut()) do
         if edgeSeq:getDestino():getInformation("type") ~= lblNodeFocus and
            edgeSeq:getDestino():getInformation("type") ~= lblNodeBrackets then

               local formulaNode = nil
               local ref = ""

               if edgeSeq:getDestino():getInformation("originalFormula") ~= nil then
                  formulaNode = edgeSeq:getDestino():getInformation("originalFormula")
                  local leftNode = sideSeq:getEdgeIn("0"):getDestino()
                  for _, edgeLeft in ipairs(leftNode:getEdgesOut()) do
                     if edgeLeft:getDestino() == formulaNode then
                        ref = edgeLeft:getInformation("reference"):getLabel()
                     end
                  end
               else
                  formulaNode = edgeSeq:getDestino()
                  if edgeSeq:getInformation("reference") ~= nil then
                     ref = edgeSeq:getInformation("reference"):getLabel()
                  end
               end

               formulaSeq = formulaNode:getLabel()..ref
               if not setOfFormulas:contains(formulaSeq) then
                  ret = false
                  break
               end
         end
      end
   end

   return ret
end

local function isExpandable(sequentNode)
   local ret = false
   local rule = ""
   local formulaNode = nil

   local rightFormulaNode = sequentNode:getEdgeOut(lblEdgeDir):getDestino():getEdgeOut("0"):getDestino()
   local typeOfNode = rightFormulaNode:getInformation("type")
   formulaNode = rightFormulaNode
   if typeOfNode == opImp.graph then
      ret = true
      rule = lblRuleImplyRight
      logger:info("isExpandable - "..sequentNode:getLabel().." ainda tem implicação `a direita.")
   end

   if not ret then
      local leftFormulasEdges = sequentNode:getEdgeOut(lblEdgeEsq):getDestino():getEdgesOut()
      local focusedFormulas = sequentNode:getInformation("focusedFormulas")

      for i=1, #leftFormulasEdges do
         formulaNode = leftFormulasEdges[i]:getDestino()
         local typeOfNode = formulaNode:getInformation("type")

         if leftFormulasEdges[i]:getLabel() ~= "0" then
            if (leftFormulasEdges[i]:getInformation("reference") == nil or leftFormulasEdges[i]:getInformation("reference") == rightFormulaNode) and
            not focusedFormulas[HelperModule.getOriginalFormulaCopied(formulaNode)] then
               ret = true
               rule = lblRuleFocus
               logger:info("isExpandable - "..sequentNode:getLabel().." ainda tem fórmulas para focar.")
               break
            end
         end
      end
   end

   if not ret then
      local focusedFormulas = sequentNode:getInformation("focusedFormulas")
      local leftExpandedFormulas = sequentNode:getInformation("leftExpandedFormulas")
      local contextFormula = sequentNode:getEdgeOut(lblEdgeDir):getDestino():getEdgeOut("0"):getDestino():getLabel()


      logger:info("isExpandable - Focused Formulas - "..sequentNode:getLabel())
      for k,v in pairs(focusedFormulas) do
         logger:info(k:getLabel())
      end

      logger:info("isExpandable - Left Expanded Formulas - "..sequentNode:getLabel())
      for k,v in pairs(leftExpandedFormulas) do
         logger:info(k)
         for formulas, _ in pairs(v) do
           logger:info(formulas:getLabel())
         end
      end

      local edgesInFocus = nil
      local edgesInOriginal = nil
      local referenceFormula = nil
      local hasReference = false

      for _,edgesInFocus in ipairs(sequentNode:getEdgeOut(lblEdgeEsq):getDestino():getEdgeOut("0"):getDestino():getEdgesOut()) do
         formulaNode = edgesInFocus:getDestino()

         if leftExpandedFormulas[contextFormula] == nil or
            not leftExpandedFormulas[contextFormula][HelperModule.getOriginalFormulaCopied(formulaNode)] and
            formulaNode:getInformation("type") == opImp.graph then

            ret = true
            rule = lblRuleImplyLeft
            logger:info("isExpandable - "..sequentNode:getLabel().." ainda tem fórmulas focada não expandida com imply-left.")
            break
         end
      end
   end

   if not ret then
      local restartedFormulas = sequentNode:getInformation("restartedFormulas")

      if restartedFormulas == nil then
         ret = true
      else
         local edgesFormulasInsideBracket = sequentNode:getEdgeOut(lblEdgeDir):getDestino():getEdgeOut("1"):getDestino():getEdgesOut()

         logger:info("Restarted Formulas - "..sequentNode:getLabel())
         for k,v in pairs(restartedFormulas) do
            logger:info(k:getLabel())
         end

         local i = #edgesFormulasInsideBracket
         while i >= 1 do
         --local i = 1
         --if #edgesFormulasInsideBracket > 0 then
            logger:info("isExpandable - "..sequentNode:getLabel().." Inside Bracket: "..edgesFormulasInsideBracket[i]:getDestino():getLabel())
            if not restartedFormulas:contains(edgesFormulasInsideBracket[i]:getDestino()) then
               logger:info("isExpandable - "..sequentNode:getLabel().." Restarted Formulas não contém "..edgesFormulasInsideBracket[i]:getDestino():getLabel())
               logger:info("isExpandable - "..sequentNode:getLabel().." ainda tem fórmulas para restartar.")
               ret = true
               rule = lblRuleRestart
               formulaNode = edgesFormulasInsideBracket[i]:getDestino()
               --break
            end
            i = i - 1
         end
      end

   end

   return ret, rule, formulaNode
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
   local edgesFocus = sequentNode:getEdgeOut(lblEdgeEsq):getDestino():getEdgeOut("0"):getDestino():getEdgesOut()
   local rightFormulaNode = sequentNode:getEdgeOut(lblEdgeDir):getDestino():getEdgeOut("0"):getDestino()
   local isAxiom = false

   for i=1, #edgesFocus do
      if edgesFocus[i]:getDestino():getInformation("type") ~= opImp.graph and
         rightFormulaNode:getInformation("type") ~= opImp.graph then
         if edgesFocus[i]:getDestino():getLabel() == rightFormulaNode:getLabel() then
            isAxiom = true
            break
         end
      end
   end

   if isAxiom then
      sequentNode:setInformation("isAxiom", true)
      sequentNode:setInformation("isExpanded", true)
      markProvedPath(sequentNode)
      return true
   else
      return false
   end
end

local function createBracketOrFocus(typeToCreate, sequentNode)
   local newNode = SequentNode:new(typeToCreate)
   graph:addNode(newNode)

   local sideNode = nil
   local edgeLabel
   if typeToCreate == lblNodeBrackets then
      sideNode = sequentNode:getEdgeOut(lblEdgeDir):getDestino()
      edgeLabel = "1"
   else
      sideNode = sequentNode:getEdgeOut(lblEdgeEsq):getDestino()
      edgeLabel = "0"
   end

   local numberOfFormulasInside = 0
   if sideNode:getEdgeOut(edgeLabel) ~= nil then
      local oldNode = sideNode:getEdgeOut(edgeLabel):getDestino()
      local copiedEdgeInsides = nil

      local listEdgesOut = oldNode:getEdgesOut()
      for i=1, #listEdgesOut do
         copiedEdgeInside = SequentEdge:new(listEdgesOut[i]:getLabel(), newNode, listEdgesOut[i]:getDestino())
         graph:addEdge(copiedEdgeInside)

         -- ERASE
         --for k,info in pairs(listEdgesOut[i]:getInformationTable()) do
         --   copiedEdgeInside:setInformation(k, info)
         --end

      end
      numberOfFormulasInside = #oldNode:getEdgesOut()
      graph:removeEdge(sideNode:getEdgeOut(edgeLabel))
   end

   return newNode, numberOfFormulasInside
end

local function findFormulaInBracket(nodeBrackets, formulaNode)
   local formulasInsideBracketEdges = nodeBrackets:getEdgesOut()
   local posFormulaInBracket = ""
   local formulaInBracketEdge = nil

   for i=1,#formulasInsideBracketEdges do
      if formulasInsideBracketEdges[i]:getDestino() == formulaNode then
         formulaInBracketEdge = formulasInsideBracketEdges[i]
         posFormulaInBracket = formulasInsideBracketEdges[i]:getLabel()
         break
      end
   end

   return formulaInBracketEdge
end

-- Public functions

function applyFocusRule(sequentNode, formulaNode)
   logger:debug("Focus: Expanding sequent "..sequentNode:getLabel().. " and formula "..formulaNode:getLabel())

   local newSequentNode, seqListNodes, seqListEdges = HelperModule.createNewSequent(sequentNode)

   graph:addNodes(seqListNodes)
   graph:addEdges(seqListEdges)
   local newEdgeDed = SequentEdge:new(lblEdgeDeducao, sequentNode, newSequentNode)

   if formulaNode:getInformation("type") == opImp.graph then
      local printFormula = HelperModule.getOriginalFormulaCopied(formulaNode)
      newEdgeDed:setInformation("rule", "\\mbox{focus}-"..opImp.tex.."_{"..printFormula:getLabel():sub(6,printFormula:getLabel():len()).."}")
   else
      newEdgeDed:setInformation("rule", "\\mbox{focus}-"..formulaNode:getLabel())
   end
   graph:addEdge(newEdgeDed)

   local newFocusNode, numberOfFormulasInside = createBracketOrFocus(lblNodeFocus, newSequentNode)

   local newFormulaNode = nil
   if formulaNode:getInformation("type") == opImp.graph then
      newFormulaNode = SequentNode:new(formulaNode:getInformation("type"))
      newFormulaNode:setInformation("originalFormula", formulaNode)
      local newEdgeEsq = SequentEdge:new(lblEdgeEsq, newFormulaNode, formulaNode:getEdgeOut(lblEdgeEsq):getDestino())
      local newEdgeDir = SequentEdge:new(lblEdgeDir, newFormulaNode, formulaNode:getEdgeOut(lblEdgeDir):getDestino())
      graph:addEdge(newEdgeEsq)
      graph:addEdge(newEdgeDir)
      graph:addNode(newFormulaNode)
   else
      newFormulaNode = formulaNode
   end

   local newEdgeFocus = SequentEdge:new(""..numberOfFormulasInside, newFocusNode, newFormulaNode)
   graph:addEdge(newEdgeFocus)

   local sequentLeftNode = newSequentNode:getEdgeOut(lblEdgeEsq):getDestino()
   local newEdgeSequent = SequentEdge:new("0", sequentLeftNode, newFocusNode)
   graph:addEdge(newEdgeSequent)

   local focusedFormulas = newSequentNode:getInformation("focusedFormulas")
   focusedFormulas:add(HelperModule.getOriginalFormulaCopied(formulaNode))

   local lweight = goalsList[sequentNode:getLabel()].weight
   goalsList[newSequentNode:getLabel()] = {goal = generateNewGoal(newSequentNode), weight = lweight}
   sequentNode:setInformation("isExpanded", true)
   logger:info("applyFocusRule - "..sequentNode:getLabel().." was expanded")

   return graph, newSequentNode, newFormulaNode
end

function applyRestartRule(sequentNode, formulaNode)
   logger:debug("Restart: Expanding sequent "..sequentNode:getLabel())

   local newSequentNode, seqListNodes, seqListEdges = HelperModule.createNewSequent(sequentNode)

   graph:addNodes(seqListNodes)
   graph:addEdges(seqListEdges)
   local newEdgeDed = SequentEdge:new(lblEdgeDeducao, sequentNode, newSequentNode)
   newEdgeDed:setInformation("rule", "\\mbox{restart}-"..formulaNode:getLabel())
   graph:addEdge(newEdgeDed)

   local formulaOutsideBracketEdge = newSequentNode:getEdgeOut(lblEdgeDir):getDestino():getEdgeOut("0")
   local newBracketNode, numberOfFormulasInside = createBracketOrFocus(lblNodeBrackets, newSequentNode)

   -- Left Side
   local sequentLeftNode = newSequentNode:getEdgeOut(lblEdgeEsq):getDestino()
   graph:removeEdge(sequentLeftNode:getEdgeOut("0"))
   local newFocusNode = SequentNode:new(lblNodeFocus)
   graph:addNode(newFocusNode)
   local newEdgeFocus = SequentEdge:new("0", sequentLeftNode, newFocusNode)
   graph:addEdge(newEdgeFocus)

   local formulaInBracketEdge = findFormulaInBracket(newBracketNode, formulaNode)
   local formulaOutsideInBracketEdge = findFormulaInBracket(newBracketNode, formulaOutsideBracketEdge:getDestino())

   local restartedFormulas = newSequentNode:getInformation("restartedFormulas")

   local listEdgesOut = sequentLeftNode:getEdgesOut()
   for i=1, #listEdgesOut do
      if listEdgesOut[i]:getLabel() ~= "0" then
         if listEdgesOut[i]:getInformation("reference") == nil then
            listEdgesOut[i]:setInformation("reference", formulaOutsideBracketEdge:getDestino())
         end

         if listEdgesOut[i]:getInformation("reference") == formulaNode then
            listEdgesOut[i]:setInformation("reference", nil)
         end
      end
   end

    -- Right Side
   local sequentRightNode = newSequentNode:getEdgeOut(lblEdgeDir):getDestino()
   local newEdgeBracket = SequentEdge:new("1", sequentRightNode, newBracketNode)

   graph:addEdge(newEdgeBracket)

   if formulaOutsideInBracketEdge ~= nil then
      graph:removeEdge(formulaOutsideInBracketEdge)
   end

   graph:removeEdge(formulaOutsideBracketEdge)
   graph:removeEdge(formulaInBracketEdge)

   local newBracketFormulaEdge = SequentEdge:new(""..contBracketFormulas, newBracketNode, formulaOutsideBracketEdge:getDestino())
   contBracketFormulas = contBracketFormulas + 1
   graph:addEdge(newBracketFormulaEdge)

   local edgeSequentToFormula = SequentEdge:new("0", newSequentNode:getEdgeOut(lblEdgeDir):getDestino(), formulaNode)
   graph:addEdge(edgeSequentToFormula)

   newSequentNode:setInformation("focusedFormulas", Set:new())

   newSequentNode:setInformation("leftExpandedFormulas", {})

   restartedFormulas:add(formulaNode)

   local lweight = goalsList[sequentNode:getLabel()].weight
   goalsList[newSequentNode:getLabel()] = {goal = generateNewGoal(newSequentNode), weight = lweight}
   sequentNode:setInformation("isExpanded", true)
   logger:info("applyRestartRule - "..sequentNode:getLabel().." was expanded")

   return graph
end

function applyImplyLeftRule(sequentNode, formulaNode)
   logger:debug("ImplyLeft: Expanding sequent "..sequentNode:getLabel().. " and formula "..formulaNode:getLabel())

   local NewSequentNode1, seqListNodes1, seqListEdges1=HelperModule.createNewSequent(sequentNode)
   local NewSequentNode2, seqListNodes2, seqListEdges2=HelperModule.createNewSequent(sequentNode)

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

   local printFormula = nil
   printFormula = HelperModule.getOriginalFormulaCopied(formulaNode)
   newEdge1:setInformation("rule", opImp.tex.."\\mbox{left}-"..opImp.tex.."_{"..printFormula:getLabel():sub(6,formulaNode:getLabel():len()).."}")
   newEdge2:setInformation("rule", opImp.tex.."\\mbox{left}-"..opImp.tex.."_{"..printFormula:getLabel():sub(6,formulaNode:getLabel():len()).."}")

   graph:addEdge(newEdge1)
   graph:addEdge(newEdge2)

   local newNodeBrackets, numberOfFormulasInside = createBracketOrFocus(lblNodeBrackets, NewSequentNode1)

   local nodeFormulaOutsideBrackets = nodeRight1:getEdgeOut("0"):getDestino()
   graph:removeEdge(nodeRight1:getEdgeOut("0"))

   local formulasInsideBracketEdges = newNodeBrackets:getEdgesOut()
   local formulaInBracketEdge = findFormulaInBracket(newNodeBrackets, nodeFormulaOutsideBrackets)

   -- 1. Create left premiss sequent:

   -- 1.0. Put label in non-marked formulas on the left
   local listEdgesOut = nodeLeft1:getEdgesOut()
   local numberOfFormulasOnLeft = #listEdgesOut
   for i=1, #listEdgesOut do
      if listEdgesOut[i]:getLabel() ~= "0" then
         if listEdgesOut[i]:getInformation("reference") == nil then
            local formulaNode = listEdgesOut[i]:getDestino()
            local newFormulaNode = nil
            if formulaNode:getEdgeOut(lblEdgeEsq) ~= nil then
               newFormulaNode = SequentNode:new(formulaNode:getInformation("type"))
               newFormulaNode:setInformation("originalFormula", formulaNode)

               local newEdgeEsq = SequentEdge:new(lblEdgeEsq, newFormulaNode, formulaNode:getEdgeOut(lblEdgeEsq):getDestino())
               local newEdgeDir = SequentEdge:new(lblEdgeDir, newFormulaNode, formulaNode:getEdgeOut(lblEdgeDir):getDestino())

               graph:addEdge(newEdgeEsq)
               graph:addEdge(newEdgeDir)
               graph:addNode(newFormulaNode)
            else
               newFormulaNode = formulaNode
            end


            local newEdgeFormula = SequentEdge:new(""..numberOfFormulasOnLeft, nodeLeft1, newFormulaNode)
            numberOfFormulasOnLeft = numberOfFormulasOnLeft + 1
            graph:addEdge(newEdgeFormula)

            newEdgeFormula:setInformation("reference", nodeFormulaOutsideBrackets)
         end
      end
   end

   -- 1.1. Put C inside bracket.
   if formulaInBracketEdge == nil then
      local newEdgeInsideBrackets = SequentEdge:new(""..contBracketFormulas, newNodeBrackets, nodeFormulaOutsideBrackets)
      contBracketFormulas = contBracketFormulas + 1
      graph:addEdge(newEdgeInsideBrackets)
   end

   local newBracketsEdge = SequentEdge:new("1", nodeRight1, newNodeBrackets)
   graph:addEdge(newBracketsEdge)

   -- 1.2. Put A (from A \to B) on the right.
   local newEdgeDir = SequentEdge:new("0", nodeRight1, formulaNode:getEdgeOut(lblEdgeEsq):getDestino())
   graph:addEdge(newEdgeDir)

   -- 2. Create right premiss sequent:

   -- 2.1. Leave A \to B on the left
   local listEdgesOut = nodeLeft2:getEdgesOut()

   -- 2.2. Add B (from A \to B) on the left outside focus
   local newFocusNode = createBracketOrFocus(lblNodeFocus, NewSequentNode2)

   local newEdgeSequent = SequentEdge:new("0", nodeLeft2, newFocusNode)
   graph:addEdge(newEdgeSequent)

   local newEdgeLeft = SequentEdge:new(""..(#nodeLeft2:getEdgesOut()+1), nodeLeft2, formulaNode:getEdgeOut(lblEdgeDir):getDestino())
   graph:addEdge(newEdgeLeft)

   local contextFormula = sequentNode:getEdgeOut(lblEdgeDir):getDestino():getEdgeOut("0"):getDestino()

   local leftExpandedFormulas = NewSequentNode1:getInformation("leftExpandedFormulas")
   if leftExpandedFormulas[contextFormula:getLabel()] == nil then
      leftExpandedFormulas[contextFormula:getLabel()] = Set:new()
   end
   local orginalFormula = HelperModule.getOriginalFormulaCopied(formulaNode)
   leftExpandedFormulas[contextFormula:getLabel()]:add(orginalFormula)

   leftExpandedFormulas = NewSequentNode2:getInformation("leftExpandedFormulas")
   if leftExpandedFormulas[contextFormula:getLabel()] == nil then
      leftExpandedFormulas[contextFormula:getLabel()] = Set:new()
   end
   leftExpandedFormulas[contextFormula:getLabel()]:add(orginalFormula)

   local lweight = goalsList[sequentNode:getLabel()].weight
   goalsList[NewSequentNode1:getLabel()] = {goal = generateNewGoal(NewSequentNode1), weight = lweight}
   goalsList[NewSequentNode2:getLabel()] = {goal = generateNewGoal(NewSequentNode2), weight = lweight+1}
   sequentNode:setInformation("isExpanded", true)
   logger:info("applyImplyLeftRule - "..sequentNode:getLabel().." was expanded")

   return graph
end

function applyImplyRightRule(sequentNode, formulaNode)
   logger:debug("ImplyRight: Expanding sequent "..sequentNode:getLabel().. " and formula "..formulaNode:getLabel())

   local NewSequentNode, seqListNodes, seqListEdges=HelperModule.createNewSequent(sequentNode)

   graph:addNodes(seqListNodes)
   graph:addEdges(seqListEdges)
   local nodeRight = NewSequentNode:getEdgeOut(lblEdgeDir):getDestino()
   local nodeLeft = NewSequentNode:getEdgeOut(lblEdgeEsq):getDestino()
   local newEdge1 = SequentEdge:new(lblEdgeDeducao, sequentNode, NewSequentNode)

   local printFormula = HelperModule.getOriginalFormulaCopied(formulaNode)
   newEdge1:setInformation("rule", opImp.tex.."\\mbox{right}-"..opImp.tex.."_{"..printFormula:getLabel():sub(6,printFormula:getLabel():len()).."}")

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

   local lweight = goalsList[sequentNode:getLabel()].weight
   goalsList[NewSequentNode:getLabel()] = {goal = generateNewGoal(NewSequentNode), weight = lweight}
   sequentNode:setInformation("isExpanded", true)
   logger:info("applyImplyRightRule - "..sequentNode:getLabel().." was expanded")

   return graph
end

function applyImplyRule(sequentNode, formulaNode)

   local sideOfOperator = verifySideOfOperator(sequentNode, formulaNode)

   if sideOfOperator == leftSide then
      return applyImplyLeftRule(sequentNode, formulaNode)
   elseif sideOfOperator == rightSide then
      return applyImplyRightRule(sequentNode, formulaNode)
   elseif sideOfOperator == nil then
      return nil
   end

   return graph
end

--- Create a graph from a formula in table form.
--- Returns a graph that represents the given formula.
--- @param seq_tabela - Formula in table form.
function LogicModule.createGraphFromTable(seq_tabela)
   local letters = {}
   sufix = 0

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
   local typeOfNode = formulaNode:getInformation("type")

   graph = agraph

   if not sequentNode:getInformation("isExpanded") then
      if typeOfNode == opImp.graph then
         graph = applyImplyRule(sequentNode, formulaNode)
      end
   end

   return true, graph
end

function LogicModule.expandAll(agraph, seqLimit, pstep)

   local isAllExpanded = true
   local k, goalEntry, focusedFormula

   -- Used to expand from a sequent
   -- if sequentNode then
   --    resetGoalsWeight(0)
   --    [sequentNode:getLabel()].weight = 1
   -- end

   graph = agraph

   table.sort(goalsList, compareGoalsListWeight)

   for k,goalEntry in pairs(goalsList) do

      --if goalEntry.weight == 1 then

         local seq = goalEntry.goal:getSequent()

         if not seq:getInformation("isExpanded") then
            logger:info("expandAll - Expanding seq "..k)

            isAllExpanded = false

            local formulaNode = nil
            local focusedFormulas = nil
            local restartedFormulas = nil
            local leftExpandedFormula = nil
            local newSeq = nil
            local leftSide = goalEntry.goal:getLeftSide()
            local rightSide = goalEntry.goal:getRightSide()
            local expanded = false
            local restarted = false
            local edgesInFocus, edgesInLeft, edgesInBracket, restartedAtom

            table.sort(leftSide, compareFormulasDegree)

            if pstep == nil then
               nstep = 1
            else
               if tonumber(pstep) <= nstep then
                  nstep = 0
                  break
               else
                  nstep = nstep + 1
               end
            end

            -- to stop debug at a specific point
            if tonumber(k:sub(4)) == 10 then
               local x = 7
            end

            if seqLimit ~= nil then
               if seqLimit == seq:getLabel():lower() then
                  logger:info("expandAll - Limit Sequent rechead!"..seq:getLabel())
                  return graph, ret
               end
            end

            if not verifyAxiom(seq) then
               local ret, rule, formulaNode = isExpandable(seq)

               if ret then
                  if rule == lblRuleImplyRight then
                     applyImplyRightRule(seq, formulaNode)
                  elseif rule == lblRuleFocus then
                     applyFocusRule(seq, formulaNode)
                  elseif rule == lblRuleImplyLeft then
                     applyImplyLeftRule(seq, formulaNode)
                  elseif rule == lblRuleRestart then
                     applyRestartRule(seq, formulaNode)
                  end

                  table.sort(goalsList, compareGoalsListWeight)
               else
                  markCounterExamplePath(seq)
                  goalsList = {}
                  nstep = 0
                  logger:info("expandAll - "..seq:getLabel().." não pode mais ser expandido.")
                  --break
               end
            end
            break
         end
      --end
   end

   local ret
   if isAllExpanded or nstep == 0 then
      nstep = 0
      sufix = sufix + 1
--      PrintModule.printGraph(graph)
--      PrintModule.printProof(graph, tostring(sufix))
      logGoalsList()
      if isAllExpanded then
         logger:info("expandAll - All sequents expanded!")
      end
      ret = true
   else
      graph = LogicModule.expandAll(graph, seqLimit, pstep)
      ret = false
   end

   return graph, ret
end

function LogicModule.getGraph()
  return graph
end

return LogicModule
