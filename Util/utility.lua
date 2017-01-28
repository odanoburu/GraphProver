-------------------------------------------------------------------------------
--   Utility Module
--
--   Contain functions that can be used by all the aplication. Normaly functions
--   for string manipulation or for debuging.
--   This is provided by the grafic module to all others that want to use this
--   functions.
--
--   @authors: Vitor, Hermann, Jefferson
--
-------------------------------------------------------------------------------

local function openFile(fileName)
   if os.capture() == "Darwin" then
      os.execute("open aux/"..fileName)                                        
   elseif os.capture() == "Linux" then
      os.execute("xdg-open aux/"..fileName)
   else
      os.execute("start aux/"..fileName)
   end
end

function os.capture()
   local f = assert(io.popen('uname', 'r'))
   local s = assert(f:read('*a'))
   f:close()
   s = string.gsub(s, '^%s+', '')
   s = string.gsub(s, '%s+$', '')
   s = string.gsub(s, '[\n\r]+', ' ')
   return s
end

function os.showGraph()
   
   if f ~= nil then
      os.execute("sfdp -x -Goverlap=scale -Tsvg aux/proofgraph.dot > aux/proofgraph.svg")
      openFile("proofgraph.svg")
   end
end

function os.showProof(nameSufix)

   if nameSufix == nil then nameSufix = "" end

   if defaultOutput == texOutputPDF then
      os.execute("pdflatex -output-directory=aux aux/prooftree"..nameSufix..".tex")
   elseif defaultOutput == texOutputHtml then
      os.execute("htlatex aux/prooftree"..nameSufix..".tex '' '' -daux/"  )
   end
   
   openFile("prooftree"..nameSufix.."."..defaultOutput)

   os.execute("rm -f prooftree*")  
end
