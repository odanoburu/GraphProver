--[[

   Main Module

   Author: Vitor, 
   Contributors: Marcela, Hermann, Jefferson

]]--

require 'constants'
require 'utility'
require 'SequentCalculusLogic'
require 'parse_input'
require 'logging.file'
require 'io' 

-- Variáveis globais do modulo
local logger, font
local SequentGraph, seqNode, nodeExpanding
local isDragging, isChoosingFocus, isExpandingFormula
local FPSCAP = 60
local text, input_formula = ""

-- Private functions

--- Dada uma aresta, ele retorna o angulo em radianos que a aresta faz com o eixo horizontal.
--- É usada para escrever textos em cima das arestas.
local function getInclinacaoAresta(edge)
   local inclinacao
   local x2Maiorx1 = false
   local y2Maiory1 = false
   local invertSignal = 1 -- para saber para onde o angulo esta virado
   local x1, y1 = edge:getOrigem():getPosition()
   local x2, y2 = edge:getDestino():getPosition()
   
   local a,b,c
   
   -- Calculando o tamanho dos lados do triangulo retangulo que a aresta forma
   -- a = hipotenusa
   -- b e c catetos
   if x1 > x2 then
      b = x1 - x2               
   elseif x2 > x1 then
      b = x2 - x1
      x2Maiorx1 = true
   else
      return math.rad(-90) -- A aresta esta na vertical
   end
   
   if y1 > y2 then
      c = y1 - y2
   elseif y2 > y1 then
      c = y2 - y1
      y2Maiory1 = true
   else
      return math.rad(0) -- A aresta esta na horizontal
   end
   
   -- Distancia entre 2 pontos
   a = math.pow(b,2) + math.pow(c,2)
   a = math.sqrt(a)
   
   -- Lei dos cossenos
   inclinacao = math.acos( (math.pow(a,2) + math.pow(b,2) - math.pow(c,2))/ (2*a*b) )
     
   -- Ajeitando a rotação para o lado correto
   if y2Maiory1 and x2Maiorx1 then
      invertSignal = 1
   elseif y2Maiory1 then
      invertSignal = -1
   elseif x2Maiorx1 then
      invertSignal = -1
   end
   
   return inclinacao * invertSignal
end

--- Um algoritmo massa-mola + carca eletrica aplicado ao grafo.
local function applyForces(graph)

   local nodes = graph:getNodes()
   local edges = graph:getEdges()

   for i=1, #nodes do
      nodes[i]:setInformation("Vx",0.0)
      nodes[i]:setInformation("Vy",0.0)
      nodes[i]:setInformation("m",0.5)
   end

   repeat               
      total_kinetic_energy = 0
      for i=1, #nodes do
         
         nodes[i]:setInformation("Fx",0.0)
         nodes[i]:setInformation("Fy",0.0)
         for j=1, #nodes do
            if i ~= j then
               dx = nodes[i]:getPositionX() - nodes[j]:getPositionX()
               dy = nodes[i]:getPositionY() - nodes[j]:getPositionY()
               rsq = (dx*dx) + (dy*dy)
               nodes[i]:setInformation("Fx",(nodes[i]:getInformation("Fx")+(100*dx/rsq)))
               nodes[i]:setInformation("Fy",(nodes[i]:getInformation("Fy")+(100*dy/rsq)))
            end
         end

         for j=1, #edges do
            local edge = edges[j]
            local nodeO = edge:getOrigem()
            local nodeD = edge:getDestino()

            if nodeO:getLabel() == nodes[i]:getLabel() or nodeD:getLabel() == nodes[i]:getLabel() then
               local Xi=0
               local Xj=0
               local Yi=0
               local Yj=0
               if nodeO:getLabel() == nodes[i]:getLabel() then
                  Xi,Yi = nodeO:getPosition()
                  Xj,Yj = nodeD:getPosition()
               else
                  Xi,Yi = nodeD:getPosition()
                  Xj,Yj = nodeO:getPosition()
               end

               dx = Xj - Xi
               dy = Yj - Yi
               nodes[i]:setInformation("Fx", nodes[i]:getInformation("Fx")+(0.06*dx))
               nodes[i]:setInformation("Fy", nodes[i]:getInformation("Fy")+(0.06*dy))
            end
         end
         nodes[i]:setInformation("Vx", (nodes[i]:getInformation("Vx")+(nodes[i]:getInformation("Fx")*0.85)))
         nodes[i]:setInformation("Vy", (nodes[i]:getInformation("Vy")+(nodes[i]:getInformation("Fy")*0.85)))
         
         nodes[i]:setPositionX(nodes[i]:getPositionX()+nodes[i]:getInformation("Vx"))
         nodes[i]:setPositionY(nodes[i]:getPositionY()+nodes[i]:getInformation("Vy"))

         total_kinetic_energy = total_kinetic_energy + (nodes[i]:getInformation("m") * ((nodes[i]:getInformation("Vx")^2) + (nodes[i]:getInformation("Vy")^2)))
      end
   until total_kinetic_energy < 50000
end

--- Ela prepara as posições (x,y) de todos os vertices para que eles possam ser desenhados.
local function prepareGraphToDraw(graph)
   
   nodes = graph:getNodes()
   
   posX = xBegin
   posY = yBegin
   
   if nodes ~= nil then
      for  i = 1, #nodes do             
         if nodes[i]:getPosition() == nil then -- só atualiza os nós que nao tem posicao.                       
            nodes[i]:setPosition(posX,posY)
            if i % 2 == 0 then
               posX = posX + 10
            else
               posY = posY + 10
            end
         end
      end
   end

   return graph
end

--- Receive a graph and draws it on the screen.
local function drawGraphEvent(graph)
   local i = 1
   
   assert( getmetatable(graph) == Graph_Metatable , "drawGraphEvent expects a graph.")
   
   local nodes = graph:getNodes()
   local edges = graph:getEdges()
   
   -- Desenha os vertices
   if nodes ~= nil then
      while i <= #nodes do
         
         local node = nodes[i]
         
         if isExpandingFormula then
           if node:getInformation("isSelected") == true then 
              love.graphics.setColor(255, 255, 0) -- Yellow circle
           end
         else        
           if node:getInformation("isProved") == nil then 
              love.graphics.setColor(204, 204, 204) -- Gray circle
           elseif node:getInformation("isProved") == false then 
              love.graphics.setColor(255, 0, 0) -- Red circle
           elseif node:getInformation("isProved") == true then 
              love.graphics.setColor(0, 255, 0) -- Green circle     
           end
           node:setInformation("isSelected", false)           
         end
         
         love.graphics.circle("fill", node:getPositionX(), node:getPositionY(), raioDoVertice, 25)
         love.graphics.setColor(0, 0, 0, 99) -- Black 99%
         love.graphics.circle("line", node:getPositionX(), node:getPositionY(), 6)
         love.graphics.print(node:getLabel(), node:getPositionX() - 10, node:getPositionY() - circleSeparation , 0, escalaLetraVertice, escalaLetraVertice )
         i = i + 1
      end
   end

   i=1
   -- Desenha as arestas
   if edges ~= nil then
      while i <= #edges do
         
         local edge = edges[i]

         love.graphics.setColor(0, 0, 0, 99) -- Black 99%
         local x1, y1 = edge:getOrigem():getPosition()
         local x2, y2 = edge:getDestino():getPosition()
         love.graphics.line(x1, y1, x2, y2)
         
         inclinacao = getInclinacaoAresta(edge)
         love.graphics.print(edge:getLabel(), (x1 + x2)/2 , (y1 + y2)/2  , inclinacao, escalaLetraAresta, escalaLetraAresta )
         
         i = i + 1
      end
   end

   applyForces(graph)
end

--- Esta função verifica se algum vertice foi clicado pelo usuário e retorna este vertice.
local function getNodeClicked() 
   -- Varrer todo o grafo procurando o vertice que pode ter sido clicado.
   nodes = SequentGraph:getNodes()      
   for i=1, #nodes do                   
      x,y = nodes[i]:getPosition()
      
      if (love.mouse.getX() <= x + raioDoVertice) and (love.mouse.getX() >= x - raioDoVertice) then
         if (love.mouse.getY() <= y + raioDoVertice) and (love.mouse.getY() >= y - raioDoVertice) then
            -- Este vertice foi clicado
            nodes[i]:setInformation("isSelected", true)
            return nodes[i]
         end
      end
   end
   return nil   
end

local function expandAll()
   if (SequentGraph ~= nil) then
      local ret, graph = LogicModule.expandAll(SequentGraph)                    
      SequentGraph= prepareGraphToDraw(graph)
   end
end

local function inputFormula()    
   logger:info("statistics -- Starting...")

   -- text = "Type your formula: ((((A imp (B)) imp (A)) imp (A)) imp (B)) imp (B)"
   -- input_formula = "((((A imp (B)) imp (A)) imp (A)) imp (B)) imp (B)"

   text = "Type your formula: ((A imp (B)) imp (A)) imp (A)"
   input_formula = "((A imp (B)) imp (A)) imp (A)"
   
   SequentGraph = LogicModule.createGraphFromTable("empty")
   prepareGraphToDraw(SequentGraph)
end

local function expandFormula()
   if (seqNode ~= nil) and (nodeExpanding ~= nil) then
      local ret, graph = LogicModule.expandNode(SequentGraph, seqNode, nodeExpanding)                    
      SequentGraph= prepareGraphToDraw(graph)
   end
end

local function printProof()   
   if SequentGraph ~= nil then
      ret = LogicModule.printProof(SequentGraph)

      if ret then
         os.execute("pdflatex -output-directory=aux aux/prooftree.tex")
         os.execute("htlatex aux/prooftree.tex '' '' -daux/"  )
         
         if os.capture() == "Darwin" then
            os.execute("open aux/prooftree.html")                                        
         elseif os.capture() == "Linux" then
            os.execute("xdg-open aux/prooftree.html")
         else
            os.execute("start aux/prooftree.html")
         end

         os.execute("rm -f prooftree*")         
      end
   end  
end

local function showInputTextEvent()
   font = love.graphics.newFont(12)

   love.graphics.setColor(0, 0, 255)
   love.graphics.setFont(font)  
   love.graphics.printf(text, 0, 0, love.graphics.getWidth())
end

local function expandAllButtonEvent()
   local xPos = windowWidth - 60
   local yPos = 5
   local xLen = 55
   local yLen = 40
   
   if love.mouse.getX() >= xPos and love.mouse.getX() <= xPos + xLen and love.mouse.getY() >= yPos and love.mouse.getY() <= yPos + yLen then    
      if love.mouse.isDown("l") then
         expandAll()
         love.timer.sleep(buttonTime)
      end
      love.graphics.setColor(100, 100, 200)
   else
      love.graphics.setColor(0, 100, 200)
   end
   love.graphics.rectangle("fill", xPos, yPos, xLen, yLen)
   love.graphics.setColor(0, 0, 255)
   love.graphics.setLineStyle("smooth")
   love.graphics.line(xPos, yPos, xPos, yPos + yLen)
   love.graphics.line(xPos, yPos + yLen, xPos + xLen, yPos + yLen)
   love.graphics.setColor(255, 255, 255)
   love.graphics.line(xPos + xLen, yPos, xPos + xLen, yPos + yLen)
   love.graphics.line(xPos, yPos, xPos + xLen, yPos)
   love.graphics.setColor(0, 0, 200)
   love.graphics.printf(expandAllButtonName, xPos + 28, yPos + 5, 0, "center")
end

local function inputFormulaButtonEvent()
   local xPos = windowWidth - 60
   local yPos = 50
   local xLen = 55
   local yLen = 40

   logger:debug("inputFormulaButtonEvent: Start")

   logger:debug("inputFormulaButtonEvent: love.mouse.getX(): "..love.mouse.getX())
   logger:debug("inputFormulaButtonEvent: love.mouse.getY(): "..love.mouse.getY())
   logger:debug("inputFormulaButtonEvent: xPos: "..xPos)
   logger:debug("inputFormulaButtonEvent: yPos: "..yPos)
   logger:debug("inputFormulaButtonEvent: yLen: "..yLen)   
   
   if love.mouse.getX() >= xPos and love.mouse.getX() <= xPos + xLen and love.mouse.getY() >= yPos and love.mouse.getY() <= yPos + yLen then
      logger:debug("inputFormulaButtonEvent: Mouse over inputFormulaButtonEvent")
      
      if love.mouse.isDown("l") then
         logger:debug("inputFormulaButtonEvent: Mouse left click over inputFormulaButtonEvent")
         inputFormula()
         love.timer.sleep(buttonTime)
      end
      love.graphics.setColor(100, 100, 200)
   else
      love.graphics.setColor(0, 100, 200)
   end
   love.graphics.rectangle("fill", xPos, yPos, xLen, yLen)
   love.graphics.setColor(0, 0, 255)
   love.graphics.setLineStyle("smooth")
   love.graphics.line(xPos, yPos, xPos, yPos + yLen)
   love.graphics.line(xPos, yPos + yLen, xPos + xLen, yPos + yLen)
   love.graphics.setColor(255, 255, 255)
   love.graphics.line(xPos + xLen, yPos, xPos + xLen, yPos + yLen)
   love.graphics.line(xPos, yPos, xPos + xLen, yPos)
   love.graphics.setColor(0, 0, 200)
   love.graphics.printf(inputFormulaButtonName, xPos + 28, yPos + 5, 0, "center")
end

local function expandFormulaButtonEvent()
   local xPos = windowWidth - 60
   local yPos = 95
   local xLen = 55
   local yLen = 40

   logger:debug("expandFormulaButtonEvent: Start")

   logger:debug("expandFormulaButtonEvent: love.mouse.getX(): "..love.mouse.getX())
   logger:debug("expandFormulaButtonEvent: love.mouse.getY(): "..love.mouse.getY())
   logger:debug("expandFormulaButtonEvent: xPos: "..xPos)
   logger:debug("expandFormulaButtonEvent: yPos: "..yPos)
   logger:debug("expandFormulaButtonEvent: yLen: "..yLen)   
   
   
   if love.mouse.getX() >= xPos and love.mouse.getX() <= xPos + xLen and love.mouse.getY() >= yPos and love.mouse.getY() <= yPos + yLen then
      logger:debug("expandFormulaButtonEvent: Mouse over expandFormulaButton")
      
      if love.mouse.isDown("l") then
         logger:debug("expandFormulaButtonEvent: Mouse left click over expandFormulaButton")
         
         isChoosingFocus = true
         love.timer.sleep(buttonTime)         
      end                        
      love.timer.sleep(buttonTime*2)
      love.graphics.setColor(100, 100, 200)
   else
      love.graphics.setColor(0, 100, 200)
   end
   love.graphics.rectangle("fill", xPos, yPos, xLen, yLen)
   love.graphics.setColor(0, 0, 255)
   love.graphics.setLineStyle("smooth")
   love.graphics.line(xPos, yPos, xPos, yPos + yLen)
   love.graphics.line(xPos, yPos + yLen, xPos + xLen, yPos + yLen)
   love.graphics.setColor(255, 255, 255)
   love.graphics.line(xPos + xLen, yPos, xPos + xLen, yPos + yLen)
   love.graphics.line(xPos, yPos, xPos + xLen, yPos)
   love.graphics.setColor(0, 0, 200)
   love.graphics.printf(expandFormulaButtonName, xPos + 28, yPos + 5, 0, "center")
end

local function printProofButtonEvent()
   local xPos = windowWidth - 60
   local yPos = 140
   local xLen = 55
   local yLen = 40
   if love.mouse.getX() >= xPos and love.mouse.getX() <= xPos + xLen and love.mouse.getY() >= yPos and love.mouse.getY() <= yPos + yLen then
      if love.mouse.isDown("l") then
         printProof()                                   
         love.timer.sleep(buttonTime)
      end
      love.graphics.setColor(100, 100, 200)
   else
      love.graphics.setColor(0, 100, 200)
   end
   love.graphics.rectangle("fill", xPos, yPos, xLen, yLen)
   love.graphics.setColor(0, 0, 255)
   love.graphics.setLineStyle("smooth")
   love.graphics.line(xPos, yPos, xPos, yPos + yLen)
   love.graphics.line(xPos, yPos + yLen, xPos + xLen, yPos + yLen)
   love.graphics.setColor(255, 255, 255)
   love.graphics.line(xPos + xLen, yPos, xPos + xLen, yPos + yLen)
   love.graphics.line(xPos, yPos, xPos + xLen, yPos)
   love.graphics.setColor(0, 0, 200)
   love.graphics.printf(printProofButtonName, xPos + 28, yPos + 5, 0, "center")
end

--- Esta função é chamada pela love.draw.
--- A todo instante ela verifica se o botão esquerdo do mouse foi apertado. Em caso positivo 
--- conforme o botão continuar sendo pressionado e caso o clique tenha sido em um vertice esta função:
--- 1- Ira alterar a posição de desenho do vertice, criando o efeito do drag and drop, ou;
--- 2- Ira mover o screen todo, ou ;
--- 3- Ira indicar um Sequent como foco (se isExpandingFormula for verdadeiro) , ou;
--- 4- Ira chamar a funcao que expande o noh (segundo o calculo lohgico implementado), se 
--- o foco (no do tipo Sequent) estiver definido.
local function dragNodeOrScreenOrSelectFocusEvent()     

   logger:debug("dragNodeOrScreenOrSelec: Start")
   
   if love.mouse.isDown("l") and isChoosingFocus then

      logger:debug("dragNodeOrScreenOrSelec: Left click, waiting for a seq node...")

      seqNode = getNodeClicked()
      
      if seqNode then

         logger:debug("dragNodeOrScreenOrSelec: Seq node chosen")         
         
         isChoosingFocus = false
         isExpandingFormula = true
         love.timer.sleep(2*buttonTime)    
      end               
      
   elseif love.mouse.isDown("l") and isExpandingFormula then

      logger:debug("dragNodeOrScreenOrSelec: Left click, waiting for a formula node...")     
      
      nodeExpanding = getNodeClicked()
      
      if nodeExpanding then

         logger:debug("dragNodeOrScreenOrSelec: Formula node chosen")
         
         isExpandingFormula = false

         expandFormula()
      end
      
   end
   if love.mouse.isDown("l") and not isDragging then            

      nodeMoving = getNodeClicked()
      isDragging = true

      xInitial = love.mouse.getX()
      yInitial = love.mouse.getY()
      -- Mudar o xInicial e o yInicial sempre que o mouse parar tb seria uma boa!

      -- Vericia se o usuário quer arrastar a tela      
   elseif not love.mouse.isDown("l") then                               
      isDragging = false
      nodeMoving = "nao vazio"
      
      -- Usuario arrastando um vertice  
   elseif nodeMoving ~= "nao vazio" and nodeMoving ~= nil then
      nodeMoving:setPosition(love.mouse.getX(), love.mouse.getY())
      --applyForces(SequentGraph)
      
      -- Usuario arrastando toda a tela 
   elseif nodeMoving == nil then        
      nodes = SequentGraph:getNodes()
      for i=1, #nodes do                        
         x,y = nodes[i]:getPosition()
         deslocamentoX = math.abs(love.mouse.getX() - xInitial)/10
         deslocamentoY = math.abs(love.mouse.getY() - yInitial)/10
         
         if love.mouse.getX() < xInitial then
            x = x - 5
         elseif love.mouse.getX() > xInitial then
            x = x + 5
         end
         
         if love.mouse.getY() < yInitial then
            y = y - 5
         elseif love.mouse.getY() > yInitial then
            y = y + 5                           
         end
         
         nodes[i]:setPosition(x, y)
      end                               
   end
end

-- Public functions: Love events

function love.keypressed(key)
   if key == "a" and love.keyboard.isDown("lctrl") then
      expandAll()
   elseif key == "i" and love.keyboard.isDown("lctrl") then
      inputFormula()
   elseif key == "p" and love.keyboard.isDown("lctrl") then
      printProof()              
   end

   if key == "backspace" then
      input_formula = input_formula:sub(1, input_formula:len()-1)
      text = "Type your formula: " .. input_formula
   end

   if key == "return" or key == "kpenter" then
      if input_formula ~= "" then
         parsed_formula = parse_input(input_formula)
         t_formula = stringtotable(parsed_formula)
         
         SequentGraph = LogicModule.createGraphFromTable(t_formula)
         prepareGraphToDraw(SequentGraph)
      end
   end
end

function love.textinput(t)
   input_formula = input_formula .. t
   text = "Type your formula: " .. input_formula
end

function love.load(arg)  
   -- Prepare to debug in ZeroBrain
   if arg[#arg] == "-debug" then
      require("mobdebug").start()
   end

   -- Log control
   logger = logging.file("aux/prover-main%s.log", "%Y-%m-%d")
   logger:setLevel(logging.DEBUG)

   -- Love initial configuration
   love.graphics.setBackgroundColor(255, 255, 255) -- White Color
   love.graphics.setColor(0, 0, 0) -- Black Color
   font = love.graphics.newFont(11)
   isDragging = false
   isChoosingFocus = false
   isExpandingFormula = false

   -- Initialize the proof graph
   SequentGraph = LogicModule.createGraphFromTable("empty")
   prepareGraphToDraw(SequentGraph)
end

function love.draw()
   showInputTextEvent()
   expandAllButtonEvent()
   inputFormulaButtonEvent()
   expandFormulaButtonEvent()    
   printProofButtonEvent()            
   drawGraphEvent(SequentGraph)
   dragNodeOrScreenOrSelectFocusEvent()         
end

