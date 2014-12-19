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

function os.capture()
   local f = assert(io.popen('uname', 'r'))
   local s = assert(f:read('*a'))
   f:close()
   s = string.gsub(s, '^%s+', '')
   s = string.gsub(s, '%s+$', '')
   s = string.gsub(s, '[\n\r]+', ' ')
   return s
end
