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
