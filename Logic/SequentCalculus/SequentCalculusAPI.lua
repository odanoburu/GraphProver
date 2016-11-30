-------------------------------------------------------------------------------
--	Sequent Calculus API Module
--
--	This module defines API functions to command line manipulation of the 
--  proof graph. 
--
--	@authors: jefferson
--
-------------------------------------------------------------------------------
require "Logic/SequentCalculus/SequentCalculusLogic"
require "Logic/SequentCalculus/NDConverter"

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

      elseif place == lblNodeBrackets then
         local bracketNode = seqNode:getEdgeOut(lblEdgeDir):getDestino():getEdgeOut("1"):getDestino()
         listEdgesOut = bracketNode:getEdgesOut()
         
      elseif place == lblNodeFocus then
         local focusNode = seqNode:getEdgeOut(lblEdgeEsq):getDestino():getEdgeOut("0"):getDestino()
         listEdgesOut = focusNode:getEdgesOut()
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
         if itemNode:getInformation("type") == lblNodeFocus then
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
   local f=loadfile("Test/commands.lua")
   f()
end

function ileft(seq, form)
   local seqNode = finds(seq)
   local formNode = findf_seq(seq, form, lblNodeFocus)

   assert(seqNode, "Sequent not found!")
   assert(formNode, "Formula have to be inside focus of the sequent!")
      
   graph = applyImplyLeftRule(seqNode, formNode)
   print_all()
   clear()
   
end

function iright(seq, form)
   local seqNode = finds(seq)
   local formNode = findf_seq(seq, form, lblEdgeDir)

   assert(seqNode, "Sequent not found!")
   assert(formNode, "Formula have to be on the right of the sequent!")
   
   graph = applyImplyRightRule(seqNode, formNode)
   print_all()
   clear()
end

function focus(seq, form)
   local seqNode = finds(seq)
   local formNode = findf_seq(seq, form, lblEdgeEsq, nil)

   assert(seqNode, "Sequent not found!")
   assert(formNode, "Formula have to be on the left of the sequent!")
   
   graph = applyFocusRule(seqNode, formNode)
   print_all()
   clear()
end

function restart(seq, form)
   local seqNode = finds(seq)
   local formNode = findf_seq(seq, form, lblNodeBrackets)

   assert(seqNode, "Sequent not found!")
   assert(formNode, "Formula have to be inside brackets of the sequent!")
   
   graph = applyRestartRule(seqNode, formNode)
   print_all()
   clear()
end

function run()
   graph = LogicModule.getGraph()
   LogicModule.expandAll(graph)
   clear()
end

function run_seq(seq)
   local seqNode = finds(seq)

   assert(seqNode, "Sequent not found!")
   
   LogicModule.expandAll(graph, nil, seqNode)
   clear()   
end

function step(pstep)
   graph = LogicModule.getGraph()
   LogicModule.expandAll(graph, pstep)
   clear()
end

function step_seq(pstep, seq)
   local seqNode = finds(seq)

   assert(seqNode, "Sequent not found!")
   
   LogicModule.expandAll(graph, pstep, seqNode)
   clear()   
end

function print_all()
   graph = LogicModule.getGraph()
   LogicModule.printProof(graph, "", true)
   os.showProofOnBrowser()   
   clear()   
end

function testc(seq)
   --graph = LogicModule.getGraph()
   local seqNode = finds(seq)
   graph = NDConverterModule.convertProof2ND(graph, seqNode)
   clear()   
end

return APIModule
