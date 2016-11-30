-------------------------------------------------------------------------------
--   Convertion of LMT Sequent Calculus into ND Module
--
--   This module defines a procedure to convert LMT Sequent Calculus proofs
--   into a pure ND proof for Minimal Implicational Logic. 
--
--   @authors: jefferson
--
-------------------------------------------------------------------------------
require "Logic/SequentCalculus/SequentCalculusLogic"
require "Logic/SequentCalculus/SequentCalculusPrint"

local logger = logging.file("aux/prover%s.log", "%Y-%m-%d")
logger:setLevel(logging.INFO)

NDConverterModule = {}


-- Private functions

function convertSequent(ndGraph, lmtSequent)
   local listNewNodes = {}
   local listNewEdges = {}
   
   local ndSequent = SequentNode:new(lmtSequent:getInformation("type"))
   listNewNodes[#listNewNodes+1] = ndSequent
   
   local ndNodeLeft = SequentNode:new(lblNodeEsq)
   local ndNodeDir = SequentNode:new(lblNodeDir)
   listNewNodes[#listNewNodes+1] = ndNodeLeft
   listNewNodes[#listNewNodes+1] = ndNodeDir

   local ndEdgeLeft = SequentEdge:new(lblEdgeEsq, ndSequent, ndNodeLeft)             
   local ndEdgeRight = SequentEdge:new(lblEdgeDir, ndSequent, ndNodeDir)
   listNewEdges[#listNewEdges+1] = ndEdgeLeft
   listNewEdges[#listNewEdges+1] = ndEdgeRight
   
 
   ndGraph:addNodes(listNewNodes)
   ndGraph:addEdges(listNewEdges)

   local ndLeftFormulas = {}

   -- Left Side
   local lmtSequentLeftNode = lmtSequent:getEdgeOut(lblEdgeEsq):getDestino()
   local lmtSequentRightNode = lmtSequent:getEdgeOut(lblEdgeDir):getDestino()
   
   local lmtListLeftEdgesOut = lmtSequentLeftNode:getEdgesOut()
   for i=1, #lmtListLeftEdgesOut do
      if lmtListLeftEdgesOut[i]:getLabel() ~= "0" then
         local referencedFormula = lmtListLeftEdgesOut[i]:getInformation("reference")

         if referencedFormula == nil then -- Delta Formula
            referencedFormula = lmtSequentRightNode:getEdgeOut("0"):getDestino()
         end

         local lmtLeftFormulas = {}
            
         if ndLeftFormulas[referencedFormula:getLabel()] then 
            lmtLeftFormulas = ndLeftFormulas[referencedFormula:getLabel()]
            lmtLeftFormulas[#lmtLeftFormulas+1] = lmtListLeftEdgesOut[i]:getDestino()
         else
            lmtLeftFormulas[#lmtLeftFormulas+1] = lmtListLeftEdgesOut[i]:getDestino()
            ndLeftFormulas[referencedFormula:getLabel()] = lmtLeftFormulas
         end
      end
   end

   return ndSequent
end

-- Public functions

function NDConverterModule.convertProof2ND(agraph, lmtSeq)
   local ndGraph = LogicModule.createGraphFromTable("empty")
   local newNDSeq = nil

   local lmtGoalEdges = agraph:getNode(lblNodeGG):getEdgesOut()
   if (lmtGoalEdges ~= nil and #lmtGoalEdges > 0) then
      local lmtGoalEdge = lmtGoalEdges[1]
      
      local lmtSeq0 = lmtGoalEdge:getDestino()
      --lmtSeq = lmtSeq0
      local ndSeq0 = convertSequent(ndGraph, lmtSeq)

      local ndGoalNode = ndGraph:getNode(lblNodeGG)      
      local ndEdgeGoal = SequentEdge:new(lblEdgeGoal, ndGoalNode, ndSeq0)      
      ndGraph:addEdge(ndEdgeGoal)   
   end

   return ndGraph
end


