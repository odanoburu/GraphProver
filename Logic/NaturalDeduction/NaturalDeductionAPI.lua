-------------------------------------------------------------------------------
--	Natural Deduction API Module
--
--	This module defines API functions to command line manipulation of the 
--  proof graph. 
--
--	@authors: jefferson, bernardo
--
-------------------------------------------------------------------------------
require "Logic/NaturalDeduction/NaturalDeductionLogic"

APIModule = {}

local graph = nil
local foundNodes = {}

-- Private functions

local function findf_sub(formNode, formStr)
	local ret = false
	local formulaNode = nil
	
	if formNode:getLabel():lower() == formStr:lower() then
		formNode:setInformation("found", true)
		table.insert(foundNodes, formNode)
		ret = true
		formulaNode = formNode
	else
		if formNode:getInformation("type") == opImp.graph then
			ret = findf_sub(formNode:getEdgeOut(lblEdgeEsq):getDestino(), formStr)
			formulaNode = formNode:getEdgeOut(lblEdgeEsq):getDestino()
			if not ret then
				ret = findf_sub(formNode:getEdgeOut(lblEdgeDir):getDestino(), formStr)
				formulaNode = formNode:getEdgeOut(lblEdgeDir):getDestino()
			end
		end
	end
	return ret, formulaNode
end

local function findf_seq(seq, form, place)
	local seqNode = finds(seq)
	local ret = nil
	local formulaNode = nil
	local listEdgesOut = nil
	
	if seqNode ~= nil then
		if place == lblEdgeEsq or place == lblEdgeDir then
			listEdgesOut = seqNode:getEdgeOut(place):getDestino():getEdgesOut()
		end

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

local function finds_ded(seqNode, seqStr)
	local foundNode = nil
	
	if seqNode ~= nil then
		if seqNode:getLabel():lower() == seqStr:lower() then
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
			
			foundNode = seqNode
		else
			if seqNode:getEdgeOut(lblEdgeDeducao) ~= nil then
				local edgesOut = seqNode:getEdgesOut()
				for i=1,#edgesOut do
					if edgesOut[i]:getLabel() == lblEdgeDeducao then
						foundNode = finds_ded(edgesOut[i]:getDestino(), seqStr)
						if foundNode then
							break
						end
					end
				end
			end
		end
	end	
	
	return foundNode	
end

-- Public Functions

function finds(seq)
  graph = LogicModule.getGraph()
	local goalEdge = graph:getNode(lblNodeGG):getEdgesOut()
	local seqNode = goalEdge[1]:getDestino()

	return finds_ded(seqNode, seq)
end

function findf(form)
  graph = LogicModule.getGraph()
	local goalEdge = graph:getNode(lblNodeGG):getEdgesOut()
	local seqNode = goalEdge[1]:getDestino()
	local found = false
	local formulaNode = nil

	while seqNode ~= nil do
		local leftSide = seqNode:getEdgeOut(lblEdgeEsq):getDestino()
		local rightSide = seqNode:getEdgeOut(lblEdgeDir):getDestino()
			
		for i=1,#leftSide:getEdgesOut() do
			local itemNode = leftSide:getEdgesOut()[i]:getDestino()
			found, formulaNode = findf_sub(itemNode, form)
			if found then
				break
			end		
		end

		if not found then
			for i=1,#rightSide:getEdgesOut() do
				local itemNode = rightSide:getEdgesOut()[i]:getDestino()
				if itemNode:getInformation("type") == lblNodeBrackets then
					local itemNodeEdges = itemNode:getEdgesOut()
					for j=1,#itemNodeEdges do
						found, formulaNode = findf_sub(itemNodeEdges:getDestino(), form)
						if found then
							break
						end
					end
				else
					found, formulaNode = findf_sub(itemNode, form)
					if found then
						break
					end
				end
			end
		end
		
		if seqNode:getEdgeOut(lblEdgeDeducao) ~= nil then
			seqNode = seqNode:getEdgeOut(lblEdgeDeducao):getDestino()
		else
			seqNode = nil
		end
	end
	
	return formulaNode
end

function clear()
	for i,v in ipairs(foundNodes) do
		v:setInformation("found", false)
	end
end

function load()
	local f = loadfile("commands.lua")
	f()
end

-- TODO modificar
function ileft(seq, form)
	local seqNode = finds(seq)
	local formNode = findf_seq(seq, form, lblNodeFocus)

	assert(seqNode, "Sequent not found!")
	assert(formNode, "Formula have to be inside focus of the sequent!")
		
	graph = applyImplyLeftRule(seqNode, formNode)
	print_all()
	clear()
end

-- TODO completar
function impIntro(form)
	local formNode = findForm(form, lblNodeImp)

	assert(formNode, "Formula was not found to apply ImplyIntro")

	graph = applyImplyIntroRule(formNode)
	print_all()
	clear()
end

function impElim(form)
	local formNode = findForm(form, lblNodeImp)

	assert(formNode, "Formula was not found to apply ImplyElim")

	graph = applyImplyElimRule(formNode)
	print_all()
	clear()
end

-- TODO modificar
function iright(seq, form)
	local seqNode = finds(seq)
	local formNode = findf_seq(seq, form, lblEdgeDir)

	assert(seqNode, "Sequent not found!")
	assert(formNode, "Formula have to be on the right of the sequent!")
	
	graph = applyImplyRightRule(seqNode, formNode)
	print_all()
	clear()
end

function run()
	LogicModule.expandAll(graph)
	clear()
end

function step(pstep)
	LogicModule.expandAll(graph, pstep)
	clear()
end

function print_all()
	PrintModule.printProof(graph, "", true)
	os.showProofOnBrowser()	
	clear()	
end

return APIModule