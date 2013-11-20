--[[

	Sequent Calculus Module

	Author: Vitor
            Bruno
            Revisado e reestruturado em 15/Dez/2012 (Hermann)
]]--

require "SequentGoalsLogic"
require "ConstantsForSequent"

-- Junta as funções que este modulo oferece como publicas.
LogicModule = {}

-- Sequente alvo da operação
local GoalSequentNode = nil


-- Private functions

--[[
	Cria um sequente novo para poder fazer uma dedução
	Cria um SeqX + um nó eX + um nó dX e aponta o eX e o dX para os mesmo lugares que o sequente dado como parametro sequentNode apontava.
	Alteracao em 3/1/2013 (Hermann): A funcao retorna o novo no do tipo sequente criado e a lista de nos e de arestas associadas a ele, 
	tambem criadas pela funcao. Anteriormente a funcao adicionava estas listas ao grafo, sem retornar valor explicito. 
	A funcao atuava via efeito colateral em graph. Atualmente nao hah mais necessidade de passar "graph" como parametro (depois vai ser retirado !!!) 
	Obs IMPORTANTE:  Esta versao aproveita os nos existentes em sequentNode sem criar novos recursos (formulas)
]]--
local function createNewSequent(graph, sequentNode)
   --  Nomes sequentNode e SequentNode sao pessimos, trocar depois (Hermann)
	local copiedSequent = nil

	local listNewNodes = {} -- todos os vertices criados ao criar o novo sequente
	local listNewEdges = {} -- todas as arestas criadas ao criar o novo sequente
	
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

local function createGraphImplyLeft()
  
-- Lendo de um arquivo/teste com Love

-- local contents = io.read()
   
-- print(contents)

-- Fim teste

	local SequentGraph = Graph:new ()
	
	NodeGG = SequentNode:new(lblNodeGG)
	NodeSeq = SequentNode:new(opSeq.graph)
	NodeEsq = SequentNode:new(lblNodeEsq)
	NodeDir = SequentNode:new(lblNodeDir)
	
	--NodeNot0 = SequentNode:new(opNot.graph)
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

local function createGraphFormula(formula_tabela,letters)

	local S2
	local S1
	local nodes
	local edges
	local FormulaGraph = Graph:new ()
	local NodeLetter=nil
	
	createDebugMessage("tabela ="..formula_tabela.tag)

-- letters contem todos os atomos.  

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
    S,L = createGraphFormula(seq_tabela, letters)
	
    createDebugMessage("RootNode ="..S.root:getLabel())
	
	local Edge1 = SequentEdge:new(lblEdgeGoal, NodeGG, NodeSeq)
	local Edge2 = SequentEdge:new(lblEdgeEsq, NodeSeq, NodeEsq)
	local Edge3 = SequentEdge:new(lblEdgeDir, NodeSeq, NodeDir)
	local Edge5 = SequentEdge:new('', NodeDir, S.root)

	local nodes = {NodeGG, NodeSeq, NodeDir, NodeEsq}
    SequentGraph:addNodes(nodes)
    SequentGraph:addNodes(S.nodes)
	local edges = {Edge1, Edge2, Edge3, Edge5}	
	SequentGraph:addEdges(edges)
	SequentGraph:addEdges(S.edges)

	goalsList[NodeSeq:getLabel()] = GoalsLogic.assembleGoalList(NodeSeq)
	return SequentGraph, goalsList
end

local function expandNodeAtomic(graph, sequentNode, node)
	local edgesLeft = sequentNode:getEdgeOut(lblEdgeEsq):getDestino():getEdgesOut()
	local edgesRight = sequentNode:getEdgeOut(lblEdgeDir):getDestino():getEdgesOut()
    local side =" "
    local isAxiom= false

	for i=1, #edgesLeft do
		if edgesLeft[i]:getDestino():getLabel() == node:getLabel() then
			side = "Left"
            break
		end
	end 
        if side == "Left" then 
          for i=1,#edgesRight do
                if edgesRight[i]:getDestino():getLabel() == node:getLabel() then 
                   isAxiom = true
                   break
                end
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
		return nil -- nao atualizarei nada
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

local function markProvedSequents(sequentNode)
	assert( getmetatable(sequentNode) == Node_Metatable , "markProvedSequents expects a node.")

	local contDed = 0

	if sequentNode:getInformation("isAxiom") == nil then
		local deductions = sequentNode:getEdgesOut()

		for i=1, #deductions do
			if deductions[i]:getLabel() == lblEdgeDeducao then
				contDed = contDed+1
				if markProvedSequents(deductions[i]:getDestino()) == false then
					return false
				end
			end
		end	
	else
		contDed = 1
	end


	if contDed > 0 then
		sequentNode:setInformation("isProved", true)
		return true
	else
		return false
	end
end

local function printFormula(formula)
	local ret = ""
	local edge, subformula = nil

	if (formula:getEdgesOut() ~= nil) and (#formula:getEdgesOut() ~= 0) then
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
	else
		ret = formula:getLabel()
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
		
		if #deductions > 0 then
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

--[[
	Funcao definida em 31-12-2012 para auxiliar no processo de debug
]]--  
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

--[[
	Create a graph from a formula in text form.
	
	Params:
		formulaText - Formula in string form.
		
	Returns:
		A graph that represents the given formula.
]]--
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

--[[
	Expand a operator in a sequent.
	For a especific graph and a node of that graph, this functions expands the node if that node is an operator.
	The operator node is only expanded if a sequent node were previusly selected.

	@param graph The graph that contains the target node.
	@param targetNode The node that you want to expand.
]]--
function LogicModule.expandNode( graph, GoalSequentNode,targetNode)
 	assert( getmetatable(targetNode) == Node_Metatable , "expandNode expects a Node") -- Garantir que é um vertice
	
	local typeOfNode = targetNode:getInformation("type")
	local wasExpanded = true

	-- Verificar se o targetNode é um operador
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

--[[
	Vai nos sequentes que ainda nao estao expandidos e faz a expancao até o final
]]--
function LogicModule.expandAll(graph, goalsList)

	local newGraph = graph		
	local isAllExpanded = true
	local ret
	
	-- loop em todos os sequentes do grafo. se achar um que nao ta expandido, expande.
	for k,goal in pairs(goalsList) do
		local seq = goal:getSequent()

		assert( getmetatable(seq) == Node_Metatable , "LogicModule.expandAll expects a Node") -- Garantir que é um vertice

		if not seq:getInformation("isExpanded") then
			isAllExpanded = false

			local formulaNode = nil			
			local leftSide = goal:getLeftSide()
			local rightSide = goal:getRightSide()
			
		 	-- TODO Extract a method for the commom code below.
			if #leftSide ~= 0 then
	            for k,formulaNode in pairs(leftSide) do 
	               ret, newGraph = LogicModule.expandNode(graph, seq, formulaNode)
	               if ret then break end
	            end
				if #rightSide ~= 0 then
					for k,formulaNode in pairs(rightSide) do 
					   ret, newGraph = LogicModule.expandNode(graph, seq, formulaNode)
					   if ret then break end
					end
				end 					
			else
		   		if #rightSide ~= 0 then
	   	            for k,formulaNode in pairs(rightSide) do 
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
				markProvedSequents(initialSequents[i]:getDestino())
			end
		end
	end
		
	return ret, newGraph	
end

function LogicModule.printProof(graph)
	assert( getmetatable(graph) == Graph_Metatable , "printProof expects a graph.")	
	
	local file = io.open("proof.tex", "w")	
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

	local numberEdgesRight = #nodeRight1:getEdgesOut()
	local labelEdgeNewFormula = numberEdgesRight
  
 	local listEdgesOut = nodeLeft1:getEdgesOut()
	for i=1, #listEdgesOut do
		if listEdgesOut[i]:getDestino():getLabel() == nodeOpImp:getLabel() then
		   graph:removeEdge(listEdgesOut[i]) -- remove a aresta que liga a direita com a implicacao objeto da regra ImpRight
		   break
		end
	end
-- Second step: updating the right side of the sequent as the antecedent of the nodeOpImp formula
    local newEdgeDir = SequentEdge:new(""..labelEdgeNewFormula, nodeRight1, nodeOpImp:getEdgeOut(lblEdgeEsq):getDestino())   
    graph:addEdge(newEdgeDir)
-- End of updating left (1) premiss

-- Updating right (2) premiss of impLeft application
-- Only one step: updating the left side of the sequent (premiss 2)  
 	local listEdgesOut = nodeLeft2:getEdgesOut()
	for i=1, #listEdgesOut do
		if listEdgesOut[i]:getDestino():getLabel() == nodeOpImp:getLabel() then
		   local labelEdgeRemoved = listEdgesOut[i]:getLabel()
		   graph:removeEdge(listEdgesOut[i]) -- remove a aresta que liga a direita com a implicacao objeto da regra ImpRight
		   break
		end
	end
	local newEdgeLeft = SequentEdge:new(labelEdgeRemoved, nodeLeft2, nodeOpImp:getEdgeOut(lblEdgeDir):getDestino()) 
	graph:addEdge(newEdgeLeft)   
-- End of updating right (2) premiss

	goalsList[NewSequentNode1:getLabel()] = GoalsLogic.assembleGoalList(NewSequentNode1)
	goalsList[NewSequentNode2:getLabel()] = GoalsLogic.assembleGoalList(NewSequentNode2)
	
	return graph, goalsList	
end

function LogicModule.expandNodeImpRight(graph, sequentNode, nodeOpImp)
	-- Passando a parte esquerda da implicacao pra esquerda do sequente.
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
		   graph:removeEdge(listEdgesOut[i]) -- remove a aresta que liga a direita com a implicacao objeto da regra ImpRight
		   break
		end
     end
	local newEdge2 = SequentEdge:new(labelEdgeRemoved, nodeRight, nodeOpImp:getEdgeOut(lblEdgeDir):getDestino())

	local numberEdgesLeft = #nodeLeft:getEdgesOut()
	local labelEdgeNewFormula = numberEdgesLeft
	local newEdge3 = SequentEdge:new(""..labelEdgeNewFormula, nodeLeft, nodeOpImp:getEdgeOut(lblEdgeEsq):getDestino())

	graph:addEdge(newEdge2)
	graph:addEdge(newEdge3)        
	
	goalsList[NewSequentNode:getLabel()] = GoalsLogic.assembleGoalList(NewSequentNode)

	return graph, goalsList	
end

--[[
	Verifica o lado do operador em relaçao ao sequente que ele participa
	@param sequentNode a node that the operatorNode should participate
	@param operatorNode a node that is the logical constant focused
	@return Return "Left" if the operatorNode is in the left side of the sequentNode
	        Return "Right" if the operatorNode is in the right side of the sequentNode
	        Return nil if the operatorNode is not part of the sequentNode
]]--
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
			-- verifica se ta na esquerda
			if verifySideOfSequent(seqEdgesOutList[i]:getDestino(), operatorNode) then
				return "Left"
			end
		end
		
		if seqEdgesOutList[i]:getLabel() == lblEdgeDir then
			-- verifica se ta na direita, pq pode nao estar em nenhum dos lados. (Usuario clicou em um operador que nao faz parte do sequente que ele tinha clicado)
			if verifySideOfSequent(seqEdgesOutList[i]:getDestino(), operatorNode) then
				return "Right"
			end
		end		
	end
	
	return nil 
end


