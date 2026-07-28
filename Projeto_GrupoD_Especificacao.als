module Projeto_GrupoD_Especificacao
open util/integer

-- ASSINATURAS

-- Representa uma partida de jogo de tabuleiro.
-- Cada partida possui um jogo, uma mesa, um horário, 
-- um conjunto de participantes e um organizador.
sig Partida {
    jogo: one Jogo,
    mesa: one Mesa,
    horario: one Horario,
    participantes: set Jogador,
    organizador: one Jogador
}

-- Representa um jogo disponível no sistema.
-- Todo jogo pertence a exatamente uma categoria.
sig Jogo {
    categoria: one Categoria
}

-- Categorias disponíveis para os jogos.
abstract sig Categoria {}

-- Existem exatamente três categorias de jogos.
one sig Estrategia extends Categoria {}
one sig Party extends Categoria {}
one sig Cooperativo extends Categoria {}

-- Representa um jogador.
sig Jogador {}

-- Representa uma mesa onde uma partida pode acontecer.
sig Mesa {}

-- Representa um horário disponível para uma partida.
sig Horario {}


-- RESTRIÇÕES DO SISTEMA

-- Um jogador não pode participar de duas partidas que aconteçam no mesmo horário.
fact SemConflitoDeHorarioParaJogador {
  all j: Jogador |
    all disj p1, p2: Partida |
      (j in p1.participantes and
       j in p2.participantes)
      implies p1.horario != p2.horario
}


-- Uma mesa não pode ser utilizada por duas partidas no mesmo horário.
fact SemConflitoDeMesa {
  all disj p1, p2: Partida |
    (p1.mesa = p2.mesa) implies (p1.horario != p2.horario)
}

-- Cada partida deve possuir entre dois e cinco participantes.
fact QuantidadeDeParticipantes {
  all p: Partida |
    #p.participantes >= 2 and #p.participantes <= 5
}

-- O organizador deve participar da própria partida que organiza.
fact OrganizadorEhParticipante {
  all p: Partida |
    p.organizador in p.participantes
}

-- Um jogador pode organizar, no máximo, duas partidas.
fact LimiteDeOrganizacao {
	all j: Jogador | #partidasOrganizadas[j] <= 2
}


-- FUNÇÕES

-- Retorna todas as partidas organizadas por um determinado jogador.
fun partidasOrganizadas[j: Jogador]: set Partida {
	{p: Partida | p.organizador = j}
}

-- Retorna todas as partidas em que um jogador participa sem ser o organizador.
fun partidasComoParticipante[j: Jogador]: set Partida {
    {p: Partida | j in p.participantes and p.organizador != j}
}


// PREDICADOS

-- Verifica se dois jogadores participaram da mesma partida.
pred jogaramJuntos[j1, j2: Jogador] {
	j1 != j2
	some p: Partida | j1 in p.participantes and j2 in p.participantes
}

-- Verifica se uma partida atingiu a capacidade máxima.
pred PartidaCheia[p: Partida] {
    #p.participantes = 5
}


-- ASSERÇÕES

-- Verifica se a quantidade de partidas não ultrapassa um limite global.
assert LimiteGlobalDePartidas {
	#Partida <= plus[#Jogador, #Jogador]
}

-- Verifica que partidas simultâneas utilizam mesas diferentes
-- e não compartilham participantes.
assert PartidasSimultaneasIsoladas {
	all disj p1, p2: Partida | p1.horario = p2.horario => {
	p1.mesa != p2.mesa
	no (p1.participantes & p2.participantes)
	}
}

check LimiteGlobalDePartidas for 5

check PartidasSimultaneasIsoladas for 5


-- CENÁRIO DE EXEMPLO
 
-- Gera um cenário contendo pelo menos uma partida.
pred CenarioExemplo {
    some Partida
}

run CenarioExemplo for 5
