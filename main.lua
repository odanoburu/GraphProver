--[[

   Main Module

   Author: Vitor, 
   Contributors: Marcela, Hermann, Jefferson

]]--

require 'constants'
require 'utility'
require 'SequentCalculusLogic'
require "logging.file"
require "io" 

-- Inicia controle de estatisticas da aplicacao.
local logger = logging.file("aux/prover%s.log", "%Y-%m-%d")
logger:setLevel(logging.INFO)

-- Love initial configuration
love.graphics.setBackgroundColor(255, 255, 255) -- White Color
love.graphics.setColor(0, 0, 0) -- Black Color
font = love.graphics.newFont(11)
isDragging = false
isChoosingFocus = false
isExpandingFormula = false

-- Private functions
--[[
   Ela prepara as posições (x,y) de todos os vertices para que eles possam ser desenhados.
]]--
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

--[[
   Chama a função de criar grafo de um determinado sistema de prova.
   Essa funcao tera que ser implementada pelo logicmodule
   Queria criar uma forma de criar uma interface para ser implementada pelo logic module
   Talvez criar uma tabela que seja LogicModule e que ela tenha funcoes a ser implementadas.
   que ai quem quiser criar um novo sistema de prova deve apenas completar os espaços.
]]--
-- Variavel privada
SequentGraph = LogicModule.createGraphFromTable("empty")
prepareGraphToDraw(SequentGraph)

--[[
   Dada uma aresta, ele retorna o angulo em radianos que a aresta faz com o eixo horizontal.
   É usada para escrever textos em cima das arestas.
]]--
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
   
   --createDebugMessage( "x1 = "..x1.." y1 = "..y1.." x2 = "..x2 .."y2 = "..y2)
   
   -- Lei dos cossenos
   inclinacao = math.acos( (math.pow(a,2) + math.pow(b,2) - math.pow(c,2))/ (2*a*b) )
   
   --createDebugMessage( "Teta = ".. (inclinacao * invertSignal) )	
   
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

--[[
Um algoritmo massa-mola + carca eletrica aplicado ao grafo.
   ]]--
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

--[[
Receive a graph and draws it on the screen.
   ]]--
local function drawGraphEvent(graph)
   local i = 1
   
   assert( getmetatable(graph) == Graph_Metatable , "drawGraphEvent expects a graph.")
   
   local nodes = graph:getNodes()
   local edges = graph:getEdges()
   
   -- Desenha os vertices
   if nodes ~= nil then
      while i <= #nodes do
	 
	 local node = nodes[i]
	 if node:getInformation("isProved") then 
	    love.graphics.setColor(0, 255, 0) -- Green circle
	 else 
	    love.graphics.setColor(204, 204, 204) -- Gray circle	
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
   
   applyForces(SequentGraph)
end

--[[
Esta função verifica se algum vertice foi clicado pelo usuário e retorna este vertice.
   ]]--
local function getNodeClicked()	
   -- Varrer todo o grafo procurando o vertice que pode ter sido clicado.
   nodes = SequentGraph:getNodes()	
   for i=1, #nodes do			
      x,y = nodes[i]:getPosition()
      
      if (love.mouse.getX() <= x + raioDoVertice) and (love.mouse.getX() >= x - raioDoVertice) then
	 if (love.mouse.getY() <= y + raioDoVertice) and (love.mouse.getY() >= y - raioDoVertice) then
	    -- Este vertice foi clicado
	    return nodes[i]
	 end
      end
   end
   return nil	
end

--[[
Em 28/02/2013 Hermann
Esta função é chamada pela love.draw.
A todo instante ela verifica se o botão esquerdo do mouse foi apertado. Em caso positivo 
   conforme o botão continuar sendo pressionado e caso o clique tenha sido em um vertice esta função:
   1- Ira alterar a posição de desenho do vertice, criando o efeito do drag and drop, ou;
	 2- Ira mover o screen todo, ou ;
	 3- Ira indicar um Sequent como foco (se isExpandingFormula for verdadeiro) , ou;
					      4- Ira chamar a funcao que expande o noh (segundo o calculo lohgico implementado), se 
					      o foco (no do tipo Sequent) estiver definido.
   ]]--
local function dragNodeOrScreenOrSelectFocusEvent()	
   
   if love.mouse.isDown("l") and isChoosingFocus then
      
      nodeFocus = getNodeClicked()
      
      if nodeFocus then 
	 isChoosingFocus = false
	 isExpandingFormula = true
	 love.timer.sleep(2*buttonTime)    
      end		
      
   elseif love.mouse.isDown("l") and isExpandingFormula then
      
      nodeExpanding = getNodeClicked()
      
      if nodeExpanding then 
	 isExpandingFormula = false
	 side = LogicModule.verifySideOfOperator(nodeFocus,nodeExpanding) 

	 if side == "Right" then 
	    SequentGraph = LogicModule.expandNodeImpRight(SequentGraph, nodeFocus, nodeExpanding)
	    SequentGraph = prepareGraphToDraw(SequentGraph)
	 elseif side == "Left" then
	    SequentGraph = LogicModule.expandNodeImpLeft(SequentGraph, nodeFocus, nodeExpanding)
	    SequentGraph = prepareGraphToDraw(SequentGraph)
	 end
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
      applyForces(SequentGraph)
      
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

function expandAll()
   createDebugMessage("Expand All called!")

   local ret, graph = LogicModule.expandAll(SequentGraph, goalsList)			
   SequentGraph= prepareGraphToDraw(graph)
end

function inputFormula() 
   -- Entra aqui quando além do if de cima o botao esquerdo foi pressionado.
   clearDebugMessages()
   createDebugMessage("Input formula called!")

   local s=require("socket")

   if client == nil then
      client,m = s.connect("localhost",8383)	
   end
   if client then							
      createDebugMessage("client connected!")

      client:send("read"..'\n')
      local input_formula = client:receive()
      t_formula = stringtotable(input_formula)				
      
      logger:info("statistics -- Starting...")    
      
      SequentGraph,goalsList = LogicModule.createGraphFromTable(t_formula)
      prepareGraphToDraw(SequentGraph)
   else 
      createDebugMessage("nao conectou, erro="..tostring(m))
   end	
end

function printProof() 
   if SequentGraph ~= nil then
      LogicModule.printProof(SequentGraph)
      os.execute("pdflatex -output-directory=aux aux/proof.tex")					
      --os.execute("xdg-open proof.pdf")
      os.execute("open aux/proof.pdf")
   end	
end

function expandAllButtonEvent()
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
   love.graphics.printf(expandAllButtonName, xPos + 30, yPos - 5, 0, "center")
end

function inputFormulaButtonEvent()
   local xPos = windowWidth - 60
   local yPos = 50
   local xLen = 55
   local yLen = 40
   
   if love.mouse.getX() >= xPos and love.mouse.getX() <= xPos + xLen and love.mouse.getY() >= yPos and love.mouse.getY() <= yPos + yLen then
      if love.mouse.isDown("l") then
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
   love.graphics.printf(inputFormulaButtonName, xPos + 30, yPos - 5, 0, "center")
end

function expandFormulaButtonEvent()
   local xPos = windowWidth - 60
   local yPos = 95
   local xLen = 55
   local yLen = 40
   if love.mouse.getX() >= xPos and love.mouse.getX() <= xPos + xLen and love.mouse.getY() >= yPos and love.mouse.getY() <= yPos + yLen then	
      if love.mouse.isDown("l") then
	 love.timer.sleep(buttonTime)
	 isChoosingFocus = true
      end                        
      love.timer.sleep(buttonTime)
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
   love.graphics.printf(expandFormulaButtonName, xPos + 30, yPos - 5, 0, "center")
end

function printProofButtonEvent()
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
   love.graphics.printf(printProofButtonName, xPos + 30, yPos - 5, 0, "center")
end

function love.keypressed(key)
   if key == "a" and love.keyboard.isDown("lctrl") then
      expandAll()
   elseif key == "i" and love.keyboard.isDown("lctrl") then
      inputFormula()
   elseif key == "p" and love.keyboard.isDown("lctrl") then
      printProof()		
   end
end

--[[
To enable debug mode
]]--
function love.load(arg)
   if arg[#arg] == "-debug" then 
      require("mobdebug").start() 
   end
end

--[[
Função do love usada para desenhar na tela todos os frames. Ela é chamada pelo love em intervalos de tempo
   muito curtos.
      ]]--
function love.draw()
   --	printDebugMessageTable(client)
   expandAllButtonEvent()
   inputFormulaButtonEvent()
   expandFormulaButtonEvent()    
   printProofButtonEvent()            
   drawGraphEvent(SequentGraph)
   dragNodeOrScreenOrSelectFocusEvent()		
end

