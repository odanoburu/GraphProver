local lpeg = require "lpeg"

local function table_atom(x)
   return (string.format("\"%s\"", x))
end

local function table_formula(f)
   if f.tag == "Atom" then 
      return("[ Atom "..table_atom(f[1]).." ]")
   elseif f.tag == "form" then 
      return("[ Imp"..table_formula(f[1])..","..table_formula(f[2]).."]")
   end 
end      

local function table_formulas(t)
   if #t > 0 then 
      local s = ""
      for i=1,#t do
	 p = p.." ( "..i..table_formula(t[i]).." ) "
      end    
   else 
      return(t.tag.."empty")
   end
end

print_Goal = function (t)
   io.write("[ Goal ")
   if #t > 0 then
      print_formulas(t[1])
      io.write(" SEQ ")
      print_formulas(t[2])
   end
   io.write("]")
end


local function print_ast(t)
   if t.tag == "Goal" then
      print_Goal(t)
   end
   print("nothing to print")
end

local function table_formula(t)
   if type(t) == "number" then 
      return(t)
   elseif type(t) == "string" then
      return(string.format("%s", t))     
   elseif type(t) == "table" then 
      local s = "{ "
      for k,v in pairs(t) do
	 s = s.."[ "..table_formula(k).."="..table_formula(v).." ]"
      end
      s = s.." }"
      return(s)
   else
      print("cannot convert table object")
   end 
end 

-- Lexical Elements
local Space = lpeg.S(" \n\t")
local skip = Space^0
local Atom = lpeg.C(lpeg.R("AZ")^1) * skip

local function getcontents(filename)
   file = assert(io.open(filename, "r"))
   contents = file:read("*a")
   file:close()
   return contents
end

local function token(pat)
   return pat * skip
end

local function kw(str)
   return token (lpeg.P(str))
end

local function symb(str)
   return token (lpeg.P(str))
end

local function taggedCap(tag, pat)
   return lpeg.Ct(lpeg.Cg(lpeg.Cc(tag), "tag") * pat)
end

function parse_input(contents)
   -- Grammar
   local formula = lpeg.V("formula")
   local form, factor, term = lpeg.V("form"), lpeg.V("factor"), lpeg.V("term")
   local Atomo = taggedCap("Atom", token(Atom))
   G = lpeg.P{ 
      formula,
      formula = skip * form * skip * -1;
      form = term + factor;
      factor = taggedCap("Atom", token(Atom)) + symb("(") * form * symb(")");
      term = taggedCap("imp", factor * kw("imp") * symb("(") * form * symb(")")); 
   }

   local t = lpeg.match(G, contents)
   if not t then
      io.write("falha no reconhecimento de ", contents)
      io.write("\n")
      os.exit(1)
   end

   ast = table_formula(t)
   return(ast)
end

