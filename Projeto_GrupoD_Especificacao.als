module Projeto_GrupoD_Especificacao
open util/integer

-- Especificação em Alloy de um sistema de gerenciamento
-- de partidas de jogos de tabuleiro em uma ludoteca.


-- ASSINATURAS

sig Partida {
    jogo: one Jogo,
    mesa: one Mesa,
    horario: one Horario,
    participantes: set Jogador,
    organizador: one Jogador
}

sig Jogo {
    categoria: one Categoria
}

abstract sig Categoria {}

one sig Estrategia extends Categoria {}
one sig Party extends Categoria {}
one sig Cooperativo extends Categoria {}

sig Jogador {}
sig Mesa {}
sig Horario {}


-- RESTRIÇÕES DO SISTEMA

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

-- Cada partida deve possuir entre dois e seis participantes.
fact QuantidadeDeParticipantes {
  all p: Partida |
    #p.participantes >= 2 and #p.participantes <= 6
}

fact OrganizadorEhParticipante {
  all p: Partida |
    p.organizador in p.participantes
}

fact LimiteDeOrganizacao {
    all j: Jogador | #partidasOrganizadas[j] <= 2
}


-- FUNÇÕES

fun partidasOrganizadas[j: Jogador]: set Partida {
    {p: Partida | p.organizador = j}
}

fun partidasComoParticipante[j: Jogador]: set Partida {
    {p: Partida | j in p.participantes and p.organizador != j}
}


-- PREDICADOS

pred jogaramJuntos[j1, j2: Jogador] {
    j1 != j2
    some p: Partida | j1 in p.participantes and j2 in p.participantes
}

-- Verifica se uma partida atingiu a capacidade máxima (6).
pred PartidaCheia[p: Partida] {
    #p.participantes = 6
}


-- ASSERÇÕES

assert LimiteGlobalDePartidas {
    #Partida <= plus[#Jogador, #Jogador]
}

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

-- TESTES DAS FUNÇÕES

-- Verifica se a função partidasOrganizadas retorna exatamente as partidas
-- organizadas por um jogador.
assert TestPartidasOrganizadas {
    all j : Jogador |
        all p : Partida |
            (p in partidasOrganizadas[j]) iff (p.organizador = j)
}

check TestPartidasOrganizadas for 5

-- Gera um cenário em que um jogador organiza uma determinada partida.
pred CenarioPartidasOrganizadas {
    some j: Jogador |
        some p: Partida |
            p.organizador = j and
            p in partidasOrganizadas[j]
}

run CenarioPartidasOrganizadas for 5


-- Verifica se a função partidasComoParticipante retorna apenas partidas
-- nas quais o jogador participa sem ser o organizador.
assert TestPartidasComoParticipante {
    all j: Jogador |
        all p: Partida |
            (p in partidasComoParticipante[j]) iff (j in p.participantes and p.organizador != j)
}

check TestPartidasComoParticipante for 5


-- Gera um cenário em que um jogador participa de uma partida sem ser seu organizador.
pred CenarioPartidasComoParticipante {
    some j: Jogador |
        some p: Partida |
            j in p.participantes and p.organizador != j and p in partidasComoParticipante[j]
}

run CenarioPartidasComoParticipante for 5


-- TESTES DOS PREDICADOS

-- Gera um cenário em que dois jogadores participaram da mesma partida.
pred CenarioJogaramJuntos {
    some j1, j2: Jogador | jogaramJuntos[j1, j2]
}

run CenarioJogaramJuntos for 5


-- Verifica se, caso dois jogadores tenham participado da mesma
-- partida, a relação permanece válida ao inverter sua ordem.
assert TestSimetriaJogaramJuntos {
    all j1, j2: Jogador | jogaramJuntos[j1, j2] => jogaramJuntos[j2, j1]
}

check TestSimetriaJogaramJuntos for 5

-- Gera um cenário em que existe uma partida cheia (com 6 participantes).
pred CenarioPartidaCheia {
    some p: Partida | PartidaCheia[p]
}

-- Definido 'for 5 but 6 Jogador' para que o Alloy crie 6 instâncias de Jogador 
-- e consiga lotar a partida com sucesso.
run CenarioPartidaCheia for 5 but 6 Jogador

