-------------------------------------------------------------------------------
--   Sequent Calculus Helper Module
--
--   Declares all necessary packages for the Logic Calculus, the data structures
--   and functions to be used by the LogicModule and the PrintModule. 
--
--   @authors: Jefferson
--
-------------------------------------------------------------------------------
require "Logic/SequentCalculus/ConstantsForSequent"
require "Logic/SequentCalculus/SequentGraph"
require "Logic/Goal"
require "Logic/Set"
require "Util/utility"
require 'ParseInput'
require "logging" 
require "logging.file"

HelperModule = {}

-- Private Functions
local function copyFocusedFormulas(sequentNode)
   local focusedFormulas = sequentNode:getInformation("focusedFormulas")
   local newFocusedFormulas = Set:new()
   for focusedFormula, _ in pairs(focusedFormulas) do
      newFocusedFormulas:add(focusedFormula)
   end

   return newFocusedFormulas
end

local function copyLeftExpandedFormulas(sequentNode)
   local leftExpandedFormulas = sequentNode:getInformation("leftExpandedFormulas")
   local newLeftExpandedFormulas = {}
   for k, v in pairs(leftExpandedFormulas) do      
      for leftExpandedFormula, _ in pairs(v) do
        if newLeftExpandedFormulas[k] == nil then
          newLeftExpandedFormulas[k] = Set:new()
        end
        newLeftExpandedFormulas[k]:add(leftExpandedFormula)
      end      
   end

   return newLeftExpandedFormulas
end

local function copyRestartedFormulas(sequentNode)
   local restartedFormulas = sequentNode:getInformation("restartedFormulas")
   local newRestartedFormulas = Set:new()
   for restartedFormula, _ in pairs(restartedFormulas) do
      newRestartedFormulas:add(restartedFormula)
   end

   return newRestartedFormulas
end


-- Public Functions
function HelperModule.getOriginalFormulaCopied(formulaNode)

   local originalFormula = nil
   
   if formulaNode:getInformation("originalFormula") == nil then
      originalFormula = formulaNode
   else
      originalFormula = HelperModule.getOriginalFormulaCopied(formulaNode:getInformation("originalFormula"))
   end
   
   return originalFormula

end

function HelperModule.countGraphElements() 
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

function HelperModule.createNewSequent(sequentNode)
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
      if esqEdgesOut[i]:getInformation("reference") ~= nil then
         newEdge:setInformation("reference", esqEdgesOut[i]:getInformation("reference"))
      end
      listNewEdges[#listNewEdges+1] = newEdge
   end

   dirEdgesOut = nodeDir:getEdgesOut()
   for i=1, #dirEdgesOut do
      local newEdge = SequentEdge:new(dirEdgesOut[i]:getLabel(), newNodeDir, dirEdgesOut[i]:getDestino())
      listNewEdges[#listNewEdges+1] = newEdge
   end

   local focusedFormulas = copyFocusedFormulas(sequentNode)
   nodeSeqNew:setInformation("focusedFormulas", focusedFormulas)

   local leftExpandedFormulas = copyLeftExpandedFormulas(sequentNode)
   nodeSeqNew:setInformation("leftExpandedFormulas", leftExpandedFormulas)

   local restartedFormulas = copyRestartedFormulas(sequentNode)
   nodeSeqNew:setInformation("restartedFormulas", restartedFormulas)     

   return nodeSeqNew,listNewNodes,listNewEdges
end
