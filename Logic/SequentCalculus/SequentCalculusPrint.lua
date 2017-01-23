-------------------------------------------------------------------------------
--   Sequent Calculus Print Module
--
--   This module defines the functions for printing proofs in Latex.
--
--   @authors: jefferson
--
-------------------------------------------------------------------------------
require "Logic/SequentCalculus/SequentCalculusHelper"

local logger = logging.file("aux/prover%s.log", "%Y-%m-%d")
logger:setLevel(logging.INFO)

PrintModule = {}

local serializedSequent = ""

-- Private functions

local function printFormula(formulaNode, shortedFormula)
   local ret = ""
   local edge, subformula = nil
   
   if shortedFormula == nil then shortedFormula = true end
      
   local formulaNumber = formulaNode:getLabel():sub(6,formulaNode:getLabel():len())
   local formulaNumberCopied = nil
   
   local originalFormula = HelperModule.getOriginalFormulaCopied(formulaNode)
   if originalFormula ~= nil then
      formulaNumber = originalFormula:getLabel():sub(6,formulaNode:getLabel():len())
      formulaNumberCopied = formulaNode:getLabel():sub(6,formulaNode:getLabel():len())
   end

   if (formulaNode:getEdgesOut() ~= nil) and (#formulaNode:getEdgesOut() ~= 0) then
      if formulaNode:getInformation("type") == lblNodeFocus then
         ret = ret.."{\\color{red}\\{}"
         for i, edge in ipairs(formulaNode:getEdgesOut()) do
            subformula = edge:getDestino()
            ret = ret..printFormula(subformula, shortedFormula)..","
         end
         ret = ret:sub(1, ret:len()-1)
         ret = ret.."{\\color{red}\\}}"
      elseif formulaNode:getInformation("type") == lblNodeBrackets then
         ret = ret.."{\\color{red}[}"
         for i, edge in ipairs(formulaNode:getEdgesOut()) do
            subformula = edge:getDestino()
            ret = ret..printFormula(subformula, shortedFormula)..","
         end
         ret = ret:sub(1, ret:len()-1)
         ret = ret.."{\\color{red}]}"
      else
         if not shortedFormula then
            for i, edge in ipairs(formulaNode:getEdgesOut()) do
               if edge:getLabel() == lblEdgeEsq then
                  subformula = edge:getDestino()
                  ret = ret.."("..printFormula(subformula, shortedFormula)
               end
            end
         end

         if originalFormula ~= nil then
            ret = ret..opImp.tex.."_{"..formulaNumber.."}^{"..formulaNumberCopied.."}"
         else
            ret = ret..opImp.tex.."_{"..formulaNumber.."}"
         end         

         if not shortedFormula then
            for i, edge in ipairs(formulaNode:getEdgesOut()) do
               if edge:getLabel() == lblEdgeDir then
                  subformula = edge:getDestino()
                  ret = ret..printFormula(subformula, shortedFormula)..")"
               end
            end
         end
      end
   else
      ret = formulaNode:getLabel()
      if formulaNode:getInformation("type") == lblNodeBrackets then
         ret = "{\\color{red}[]}"
      end
      if formulaNode:getInformation("type") == lblNodeFocus then
         ret = "{\\color{red}\\{\\}}"
      end      
   end

   return ret

end

local function printSequent(sequentNode, file, printOnlyOpenBranch)
   local ret = ""
   local edge, nodeEsq, nodeDir = nil
   local deductions = {}
   local j = 1
   local rule = ""
   local shortedFormula = printShortedFormulas
   local alreadyPrintedFormulas = Set:new()

   if sequentNode ~= nil then

      -- to stop debug at a specific point
      if tonumber(sequentNode:getLabel():sub(4)) == 4 then
         local x = 10
      end          

      
      local seqNumber = sequentNode:getLabel():sub(4,sequentNode:getLabel():len())
      if seqNumber == "0" then shortedFormula = false end
      
      for i, edge in ipairs(sequentNode:getEdgesOut()) do       
         if edge:getLabel() == lblEdgeEsq then
            nodeEsq = edge:getDestino()
         end
         if edge:getLabel() == lblEdgeDir then
            nodeDir = edge:getDestino()
         end
         if edge:getLabel() == lblEdgeDeducao then
            local seqDed = edge:getDestino()
            deductions[j] = seqDed
            rule = edge:getInformation("rule")
            j = j+1
         end                    
      end

      if #deductions > 0 then
         file:write("\\prftree[r]{$"..rule.."$}\n")
      end      

      -- Premisses

      --serializedSequent = serializedSequent..ret.." "  
      if #deductions > 0 then
         --serializedSequent = serializedSequent:sub(1, serializedSequent:len()-1)
         --serializedSequent = serializedSequent.."|"
         
         for i, nextSeqNode in ipairs(deductions) do           
            if printOnlyOpenBranch then
               -- Print dots in the branch that is not totally expanded or is closed.
               if nextSeqNode:getInformation("isProved") ==nil or sequentNode:getInformation("isProved") then
                  file:write("{\\vdots}\n")               
               else
                  file:write("{\n")            
                  printSequent(deductions[i], file, printOnlyOpenBranch)
                  file:write("\n}\n")
               end
            else
               file:write("{\n")            
               printSequent(deductions[i], file, printOnlyOpenBranch)
               file:write("\n}\n")               
            end            
         end         
      end

      -- Conclusion

      if sequentNode:getInformation("isAxiom") then
         file:write("{\\color{blue}{")
      elseif sequentNode:getInformation("isProved") ~= nil and not sequentNode:getInformation("isProved") then
         file:write("{\\color{red}{")
      else            
         file:write("{")
      end      

      -- Left side
      if nodeEsq ~= nil then
         for i, edge in ipairs(nodeEsq:getEdgesOut()) do
            local formulaNode = edge:getDestino()
            local atomicReference = edge:getInformation("reference") 
            
            local formulaAsStr = printFormula(formulaNode, shortedFormula)
            local contextAsStr = HelperModule.getOriginalFormulaCopied(formulaNode):getLabel()

            if atomicReference ~= nil then
               if shortedFormula then
                  formulaAsStr = "("..formulaAsStr..")^{"..atomicReference:getLabel().."}"
               else
                  formulaAsStr = formulaAsStr.."^{"..atomicReference:getLabel().."}"
               end
               contextAsStr = contextAsStr..atomicReference:getLabel()
            end
            
            if not alreadyPrintedFormulas:contains(contextAsStr) then
               ret = ret..formulaAsStr
               alreadyPrintedFormulas:add(contextAsStr)
               ret = ret..","
            end              
         end    
         ret = ret:sub(1, ret:len()-1)
      end

      -- Sequent Symbol
      ret = ret.." {\\color{blue}"..opSeq.tex.."_{"..seqNumber.."}} "


      -- Right Side
      edge = nil
      for i, edge in ipairs(nodeDir:getEdgesOut()) do
         ret = ret..printFormula(edge:getDestino(), shortedFormula)
         ret = ret..","
      end       
      ret = ret:sub(1, ret:len()-1)     

      file:write(ret)
      if sequentNode:getInformation("isAxiom") or
         ( sequentNode:getInformation("isProved") ~= nil and not sequentNode:getInformation("isProved")) then
         file:write("}}")
      else            
         file:write("}")
      end

   end
end

-- Public functions

function PrintModule.printProof(agraph, nameSufix)

   if nameSufix == nil then nameSufix = "" end
   
   local texOutput = defaultOutput
   
   local file = io.open("aux/prooftree"..nameSufix..".tex", "w")
   local goalEdge = agraph:getNode(lblNodeGG):getEdgesOut()
   local ret = false

   if (goalEdge ~= nil) and (#goalEdge > 0) then
      
      local seq = goalEdge[1]:getDestino()

      file:write("\\documentclass[landscape]{article}\n\n")

      file:write("\\usepackage{etex}\n")      
      file:write("\\usepackage{amsbsy}\n")
      file:write("\\usepackage{color}\n")
      file:write("\\usepackage[ND,SEQ]{prftree}\n")
      
      if texOutput == texOutputPDF then
         file:write("\\usepackage{incgraph}\n\n")
      end 
      file:write("\\begin{document}\n")
      if texOutput == texOutputPDF then
         file:write("\\begin{inctext}\n")
      end

      if seq:getEdgeOut(lblEdgeDeducao) ~= nil then
         file:write("$$\n")
      else
         file:write("$")
      end

      -- If Seq0 is false, print only the open branch
      if seq:getInformation("isProved") ~= nil and not seq:getInformation("isProved") then
         printOnlyOpenBranch = true
      else
         printOnlyOpenBranch = false         
      end
      
      printSequent(seq, file, printOnlyOpenBranch)
      
      --serializedSequent = serializedSequent:gsub("\\vdash", "⊨")
      --serializedSequent = serializedSequent:gsub("\\to", "→")
      --logger:info("statistics -- Serialized sequent: "..serializedSequent)  
      --logger:info("statistics -- Size of serialized sequent: "..serializedSequent:len())  
      --countGraphElements()

      if seq:getEdgeOut(lblEdgeDeducao) ~= nil then
         file:write("\n$$\n")
      else
         file:write("$\n")
      end

      if texOutput == texOutputPDF then
         file:write("\\end{inctext}\n")
      end
      file:write("\\end{document}\n")
      file:close()

      ret = true
      os.showProof(nameSufix)
   end
  
   return ret
end
