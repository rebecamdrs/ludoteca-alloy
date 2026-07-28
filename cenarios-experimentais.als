module Cenarios_Experimentais
open Projeto_GrupoD_Especificacao

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

-- Gera um cenário em que dois jogadores participaram da mesma partidas.
pred CenarioJogaramJuntos {
    some j1, j2: Jogador | jogaramJuntos[j1, j2]
}
run CenarioJogaramJuntos for 5


-- Verifica se a relação "jogaram juntos" é simétrica.
assert TestSimetriaJogaramJuntos {
    all j1, j2: Jogador | jogaramJuntos[j1, j2] => jogaramJuntos[j2, j1]
}

check TestSimetriaJogaramJuntos for 5

assert NenhumaPartidaSuperlotada {
    all p: Partida | not (#p.participantes > 5)
}
check NenhumaPartidaSuperlotada for 5

assert TestMaximoParticipantes {
    all p: Partida | #p.participantes <= 5
}
check TestMaximoParticipantes for 5


-- Verifica se existe uma partida com o número máximo de participantes.
pred CenarioPartidaCheia {
    some p: Partida | PartidaCheia[p]
}
run CenarioPartidaCheia for 5
