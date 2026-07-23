module Projeto_GrupoD_Especificacao
open util/integer

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

fact SemConflitoDeHorarioParaJogador {
  all j: Jogador |
    all disj p1, p2: Partida |
      (j in p1.participantes  and
       j in p2.participantes)
      implies p1.horario != p2.horario
}

fact SemConflitoDeMesa {
  all disj p1, p2: Partida |
    (p1.mesa = p2.mesa) implies (p1.horario != p2.horario)
}

fact QuantidadeDeParticipantes {
  all p: Partida |
    #p.participantes >= 2 and #p.participantes <= 6
}

fact OrganizadorEhParticipante {
  all p: Partida |
    p.organizador in p.participantes
}

fun partidasOrganizadas[j: Jogador]: set Partida {
	{p: Partida | p.organizador = j}
}

fun partidasComoParticipante[j: Jogador]: set Partida {
    {p: Partida | j in p.participantes and p.organizador != j}
}

pred jogaramJuntos[j1, j2: Jogador] {
	j1 != j2
	some p: Partida | j1 in p.participantes and j2 in p.participantes
}

fact LimiteDeOrganizacao {
	all j: Jogador | #partidasOrganizadas[j] <= 2
}

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

pred CenarioExemplo {
    some Partida
}
run CenarioExemplo for 5
