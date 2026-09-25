#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Monitor de citas DIAN -> alerta por WhatsApp (CallMeBot).

Vigila el agendamiento de https://agendamiento.dian.gov.co/ para la
combinacion:  Persona Natural + Videoatencion + Devoluciones.

Como funciona (sin navegador, solo HTTP):
  1. GET /                              -> extrae el token anti-CSRF "anticsrf"
                                           (es de un solo uso, se pide uno nuevo
                                           para cada POST).
  2. POST /Player.aspx/ObtenerConfiguracion
                                        -> devuelve la definicion del player,
                                           de donde sale el token cifrado
                                           "ConfiguracionServicioRestEncriptado".
                                           Se pide UNA sola vez por corrida y se
                                           reutiliza en todos los sondeos.
  3. POST /Player.aspx/ValidadorValidar
                                        -> con el manejador "manejadorEncontroColas"
                                           devuelve los tramites disponibles.
                                           Encontrado=true  -> HAY cita
                                           Encontrado=false -> no hay

RITMO ADAPTATIVO
GitHub Actions no puede disparar mas seguido que cada 5 minutos, asi que el
workflow corre cada 5 minutos y es este script el que decide, segun el dia y la
hora de Bogota, si revisa y cuantas veces revisa dentro de la misma corrida.

Segun la experiencia reportada, la DIAN abre cupos sobre todo los VIERNES
(alrededor de las 9:30 am, y alguna vez a las 3 pm) y suelta cancelaciones los
MARTES y MIERCOLES.

  ALTA    viernes 8:30-12:30 y 14:00-17:00   -> 4 sondeos por corrida (~75 seg)
  MEDIA   martes y miercoles 8:00-17:00      -> 1 sondeo cada 5 minutos
          viernes, resto de 7:00-19:00
  NORMAL  lunes y jueves 8:00-17:00          -> 1 sondeo cada 10 minutos
  BAJA    resto de dias habiles 6:00-21:00   -> 1 sondeo cada 20 minutos
  MINIMA  noches y fines de semana           -> 1 sondeo cada 30 minutos

PRUDENCIA (para no molestar al servidor de la DIAN ni terminar bloqueados)
  - Espera aleatoria de unos segundos al arrancar, para no pegarle al servidor
    en el segundo exacto cada vez.
  - Reutiliza el token cifrado dentro de la corrida: el primer sondeo cuesta 3
    peticiones y los siguientes solo 2.
  - En la ventana mas intensa esto son unas 2 peticiones por minuto, comparable
    a una persona refrescando la pagina.
  - Si la DIAN responde 403 o 429 (bloqueo o "muy rapido"), corta la corrida de
    inmediato y no insiste. Dos cortes seguidos y entra en modo prudente.
  - Fuera de las ventanas buenas casi no consulta.

Estado: guarda en state.json los tramites ya avisados para no repetir la
alerta en cada corrida mientras el cupo siga abierto.
"""

import json
import os
import random
import re
import sys
import time
import html as htmllib
import urllib.parse
import smtplib
from email.mime.text import MIMEText
from datetime import datetime, timezone, timedelta

import requests

# ----------------------------------------------------------------------------
# Configuracion (todo se puede sobreescribir con variables de entorno)
# ----------------------------------------------------------------------------

BASE = "https://agendamiento.dian.gov.co"
RUTA_RECURSOS = "Recursos/CitasDIAN/"

# Codigos descubiertos en la propia app de la DIAN:
#   Tipo de persona : 1 = Persona Natural, 2 = Persona Juridica
#   Tipo de atencion: 1 = Presencial,      2 = Virtual (Videoatencion)
#   Categoria       : 7  = RUT y orientacion TAC
#                     11 = Conferencias o capacitaciones
#                     13 = Devoluciones           <-- el que nos interesa
#                     15 = Autogestion servicios en linea con NAF
#                     16 = Inconsistencias Grandes Contribuyentes
#                     17 = Cobranzas
#                     19 = Defensoria
TIPO_PERSONA = os.environ.get("DIAN_TIPO_PERSONA", "1")
TIPO_ATENCION = os.environ.get("DIAN_TIPO_ATENCION", "2")
CATEGORIA = os.environ.get("DIAN_CATEGORIA", "13")

# Filtro opcional por texto (ej. "Bogot"). Vacio = avisa por cualquier ciudad.
FILTRO = os.environ.get("DIAN_FILTRO", "").strip()

# CallMeBot
WA_PHONE = os.environ.get("CALLMEBOT_PHONE", "").strip()
WA_APIKEY = os.environ.get("CALLMEBOT_APIKEY", "").strip()

# Correo (Gmail con contrasena de aplicacion)
GMAIL_USER = os.environ.get("GMAIL_USER", "").strip()
GMAIL_PASS = os.environ.get("GMAIL_PASS", "").replace(" ", "").strip()
MAIL_TO = os.environ.get("MAIL_TO", "").strip() or GMAIL_USER

# Poner "1" para mandar un correo de prueba al iniciar (desde Run workflow)
PROBAR_CORREO = os.environ.get("DIAN_PROBAR_CORREO", "").strip().lower() in ("1", "true")

STATE_FILE = os.environ.get("DIAN_STATE_FILE", "state.json")

# Cuantas corridas fallidas seguidas antes de avisar que el bot esta roto
FALLOS_ANTES_DE_AVISAR = int(os.environ.get("DIAN_FALLOS_ANTES_DE_AVISAR", "8"))

# Poner "1" para forzar un sondeo ignorando el horario (util para probar)
FORZAR = os.environ.get("DIAN_FORZAR", "").strip() == "1"

# Segundos de margen: la corrida nunca debe pasarse del hueco de 5 minutos
PRESUPUESTO_SEG = int(os.environ.get("DIAN_PRESUPUESTO_SEG", "210"))

TIMEOUT = 30
REINTENTOS = 2

UA = (
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/140.0.0.0 Safari/537.36"
)

BOGOTA = timezone(timedelta(hours=-5))


def ahora_dt():
    return datetime.now(BOGOTA)


def ahora():
    return ahora_dt().strftime("%Y-%m-%d %H:%M:%S")


def log(msg):
    print("[{}] {}".format(ahora(), msg), flush=True)


class Bloqueado(Exception):
    """La DIAN respondio 403/429: hay que parar y no insistir."""


# ----------------------------------------------------------------------------
# Ritmo adaptativo
# ----------------------------------------------------------------------------

DIAS = ["lunes", "martes", "miercoles", "jueves", "viernes", "sabado", "domingo"]


def plan_de_sondeo(now):
    """Devuelve (etiqueta, numero_de_sondeos, segundos_entre_sondeos) o None."""
    dow = now.weekday()          # 0 = lunes ... 4 = viernes, 5-6 = fin de semana
    m = now.hour * 60 + now.minute
    minuto = now.minute

    def en(desde, hasta):
        return desde <= m < hasta

    # Viernes, ventanas calientes: 8:30-12:30 y 14:00-17:00
    if dow == 4 and (en(8 * 60 + 30, 12 * 60 + 30) or en(14 * 60, 17 * 60)):
        return ("ALTA", 4, 75)

    # Martes y miercoles: sueltan las cancelaciones
    if dow in (1, 2) and en(8 * 60, 17 * 60):
        return ("MEDIA", 1, 0)

    # Viernes, resto de la jornada
    if dow == 4 and en(7 * 60, 19 * 60):
        return ("MEDIA", 1, 0)

    # Lunes y jueves en horario habil: cada 10 minutos
    if dow in (0, 3) and en(8 * 60, 17 * 60):
        return ("NORMAL", 1, 0) if minuto % 10 < 5 else None

    # Resto de dias habiles, horario amplio: cada 20 minutos
    if dow <= 4 and en(6 * 60, 21 * 60):
        return ("BAJA", 1, 0) if minuto % 20 < 5 else None

    # Noches y fines de semana: cada 30 minutos
    return ("MINIMA", 1, 0) if minuto % 30 < 5 else None


# ----------------------------------------------------------------------------
# Cliente DIAN
# ----------------------------------------------------------------------------

class DianClient:
    def __init__(self):
        self.s = requests.Session()
        self.s.headers.update({
            "User-Agent": UA,
            "Accept-Language": "es-CO,es;q=0.9",
        })
        self._enc_token = None
        self.peticiones = 0

    def _anticsrf(self):
        """El token es de un solo uso: se pide uno nuevo antes de cada POST."""
        r = self.s.get(BASE + "/", timeout=TIMEOUT)
        self.peticiones += 1
        if r.status_code in (403, 429):
            raise Bloqueado("GET / devolvio HTTP {}".format(r.status_code))
        r.raise_for_status()
        m = re.search(r'name="anticsrf"[^>]*value="([^"]+)"', r.text)
        if not m:
            raise RuntimeError("No se encontro el token anticsrf en el HTML")
        return m.group(1)

    def _post(self, metodo, payload):
        headers = {
            "Content-Type": "application/json; charset=utf-8",
            "Accept": "application/json, text/javascript, */*; q=0.01",
            "X-Requested-With": "XMLHttpRequest",
            "Referer": BASE + "/",
            "RequestVerificationToken": self._anticsrf(),
            "g-recaptcha-response": "",
        }
        r = self.s.post(
            "{}/Player.aspx/{}".format(BASE, metodo),
            headers=headers,
            data=json.dumps(payload),
            timeout=TIMEOUT,
        )
        self.peticiones += 1
        if r.status_code in (403, 429):
            raise Bloqueado("{} devolvio HTTP {}".format(metodo, r.status_code))
        if r.status_code != 200:
            raise RuntimeError(
                "{} devolvio HTTP {}: {}".format(metodo, r.status_code, r.text[:200])
            )
        # Las page methods de ASP.NET envuelven la respuesta en {"d": "<json>"}
        outer = r.json()
        return json.loads(outer["d"]) if isinstance(outer.get("d"), str) else outer["d"]

    def token_cifrado(self):
        """Se pide una sola vez por corrida y se reutiliza en cada sondeo."""
        if self._enc_token:
            return self._enc_token
        data = self._post(
            "ObtenerConfiguracion",
            {"rutaRecurso": RUTA_RECURSOS, "nombreRecurso": ""},
        )
        raw = data if isinstance(data, str) else json.dumps(data, ensure_ascii=False)
        m = re.search(
            r'"ConfiguracionServicioRestEncriptado"\s*:\s*"([^"]+)"', raw)
        if not m:
            raise RuntimeError("No se encontro ConfiguracionServicioRestEncriptado")
        self._enc_token = m.group(1)
        return self._enc_token

    def _configuracion(self):
        return {
            "ConfiguracionServicioRestEncriptado": self.token_cifrado(),
            "ControlesGeolocalizacion": [],
            "FormatoCitas": "{cita.codigo}    {cita.fecha}    {cita.Oficina.Nombre}",
            "IdPais": 1,
            "DistanciaMinima": 0,
            "TopOficinasCercanas": 0,
            "FormatoEncabezadoOficina": "",
            "FormatoOficina": "{0}",
            "ModoWebPlayer": True,
            "Archivo": {
                "Ruta": RUTA_RECURSOS,
                "FechaActualizacion": "2026-09-09T12:19:00.5196151-05:00",
            },
            "TipoPolitica": 0,
            "ObtenerEspecialidadesVirtuales": False,
            "ObtenerEspecialidadesPresenciales": False,
            "GenerarTurno": False,
        }

    def consultar_tramites(self, tipo_persona, categoria, tipo_atencion):
        """Devuelve la lista de tramites con cupo. Lista vacia = no hay cita."""
        cita = {
            "CodigoCita": None,
            "CodigoCitaModificada": None,
            "Cola": {"IdEspecialidad": "0", "Nombre": None},
            "TipoEspecialidad": {
                "IdTipoEspecialidad": int(tipo_atencion),
                "Nombre": "Virtual" if str(tipo_atencion) == "2" else "Presencial",
            },
            "Oficina": {"IdOficina": "001", "Nombre": None, "Latitud": 0, "Longitud": 0},
            "UsuarioCliente": {
                "IdTipoCliente": str(tipo_persona),
                "IdTipoDocumento": 0,
                "Nombre": None, "Apellido": None, "NumeroDocumento": None,
                "CorreoElectronico": None, "Celular": None, "Telefono": None,
                "Direccion": None, "IdCiudad": 0, "IdEstado": 0,
                "AceptaPoliticaDatos": False,
            },
            "Fecha": "2001-01-01T17:00:00.000Z",
            "Hora": "2001-01-01T17:00:00.000Z",
            "IdAgenda": 0,
            "Estado": {"IdEstado": 0, "Nombre": None},
            "Funcionario": {"NombreAMostrar": None, "Id": None},
            "Archivo": None,
            "CamposAdicionales": None,
            "EsFlujoCitaCreacion": "true",
        }
        payload = {
            "nombre": "ValidadorDatos.CitasWeb",
            "configuracion": self._configuracion(),
            "respuestaBase": {
                "Fuente": "Validador",
                "Encontrado": False,
                "DetalleAdicional": "manejadorEncontroColas",
                "ObjetosEncontrados": [
                    json.dumps(cita),
                    "Nombre",
                    str(tipo_persona),
                    str(categoria),
                    str(tipo_atencion),
                ],
                "Recurso": "CitasDIAN",
            },
        }
        data = self._post("ValidadorValidar", payload)
        if not data.get("Encontrado"):
            return []
        grupos = data.get("ObjetosEncontrados") or []
        items = grupos[0] if grupos and isinstance(grupos[0], list) else grupos
        return [limpiar(x.get("Nombre", "")) for x in items if isinstance(x, dict)]


def limpiar(txt):
    return htmllib.unescape(re.sub(r"\s+", " ", str(txt))).strip()


# ----------------------------------------------------------------------------
# WhatsApp (CallMeBot)
# ----------------------------------------------------------------------------

def enviar_correo(texto):
    """Manda el aviso por correo (Gmail). Devuelve True si salio bien."""
    if not GMAIL_USER or not GMAIL_PASS or not MAIL_TO:
        log("AVISO: faltan GMAIL_USER / GMAIL_PASS / MAIL_TO, no se envia correo.")
        return False
    asunto = texto.strip().splitlines()[0][:120] if texto.strip() else "Bot DIAN"
    msg = MIMEText(texto, "plain", "utf-8")
    msg["Subject"] = "\U0001F6A8 " + asunto
    msg["From"] = GMAIL_USER
    msg["To"] = MAIL_TO
    for intento in range(1, 4):
        try:
            with smtplib.SMTP_SSL("smtp.gmail.com", 465, timeout=TIMEOUT) as srv:
                srv.login(GMAIL_USER, GMAIL_PASS)
                srv.sendmail(GMAIL_USER, [MAIL_TO], msg.as_string())
            log("Correo enviado a {}.".format(MAIL_TO))
            return True
        except Exception as e:
            log("Error enviando correo (intento {}): {}".format(intento, e))
            time.sleep(3 * intento)
    return False


def enviar_whatsapp(texto):
    # Primero el correo (el WhatsApp de CallMeBot puede fallar)
    enviar_correo(texto)
    if not WA_PHONE or not WA_APIKEY:
        log("AVISO: faltan CALLMEBOT_PHONE / CALLMEBOT_APIKEY, no se envia nada.")
        log("Mensaje que se habria enviado:\n" + texto)
        return False
    url = "https://api.callmebot.com/whatsapp.php?" + urllib.parse.urlencode({
        "phone": WA_PHONE,
        "text": texto,
        "apikey": WA_APIKEY,
    })
    for intento in range(1, 4):
        try:
            r = requests.get(url, timeout=TIMEOUT)
            if r.status_code == 200:
                log("WhatsApp enviado.")
                return True
            log("CallMeBot HTTP {} (intento {}): {}".format(
                r.status_code, intento, r.text[:200]))
        except Exception as e:
            log("Error enviando WhatsApp (intento {}): {}".format(intento, e))
        time.sleep(3 * intento)
    return False


# ----------------------------------------------------------------------------
# Estado
# ----------------------------------------------------------------------------

def estado_vacio():
    return {"avisados": [], "fallos": 0, "ultima_revision": None,
            "ultimo_error": None, "aviso_fallo_enviado": False,
            "bloqueos": 0, "ultimo_plan": None}


def leer_estado():
    try:
        with open(STATE_FILE, "r", encoding="utf-8") as f:
            st = json.load(f)
        base = estado_vacio()
        base.update(st)
        return base
    except Exception:
        return estado_vacio()


def guardar_estado(st):
    st["ultima_revision"] = ahora()
    with open(STATE_FILE, "w", encoding="utf-8") as f:
        json.dump(st, f, ensure_ascii=False, indent=2)


# ----------------------------------------------------------------------------
# Main
# ----------------------------------------------------------------------------

NOMBRE_ATENCION = {"1": "Presencial", "2": "Videoatencion"}
NOMBRE_CATEGORIA = {
    "7": "RUT y orientacion TAC", "11": "Conferencias o capacitaciones",
    "13": "Devoluciones", "15": "Autogestion servicios en linea con NAF",
    "16": "Inconsistencias Grandes Contribuyentes", "17": "Cobranzas",
    "19": "Defensoria",
}


def etiqueta_busqueda():
    return "{} / {} / {}".format(
        "Persona Natural" if TIPO_PERSONA == "1" else "Persona Juridica",
        NOMBRE_ATENCION.get(TIPO_ATENCION, TIPO_ATENCION),
        NOMBRE_CATEGORIA.get(CATEGORIA, CATEGORIA),
    )


def avisar(tramites, st):
    """Manda el WhatsApp solo si hay algo que no se haya avisado antes."""
    nuevos = [t for t in tramites if t not in st.get("avisados", [])]
    if not nuevos:
        log("Hay cupo pero ya te avise de estos tramites. No repito.")
        return False
    lineas = "\n".join("- " + t for t in tramites)
    mensaje = (
        "HAY CITA EN LA DIAN\n\n"
        "{}\n\n"
        "Tramites disponibles:\n{}\n\n"
        "Agenda ya: https://agendamiento.dian.gov.co/\n"
        "Ruta: Agendar cita > Persona Natural > Videoatencion > Devoluciones\n\n"
        "({})"
    ).format(etiqueta_busqueda(), lineas, ahora())
    enviar_whatsapp(mensaje)
    st["avisados"] = tramites
    return True


def main():
    if PROBAR_CORREO:
        ok = enviar_correo(
            "PRUEBA Bot DIAN: el aviso por correo funciona\n\n"
            "Si recibes este correo, cuando aparezca cupo te llegara un aviso asi.\n"
            "({})".format(ahora()))
        log("Correo de prueba: {}".format("OK" if ok else "FALLO"))
        if not ok:
            return 1
    st = leer_estado()
    now = ahora_dt()

    plan = ("FORZADO", 1, 0) if FORZAR else plan_de_sondeo(now)
    if plan is None:
        log("{} {} - fuera de ventana, no consulto (asi no molestamos a la DIAN)."
            .format(DIAS[now.weekday()], now.strftime("%H:%M")))
        return 0

    etiqueta_plan, n_sondeos, espaciado = plan

    # Si venimos de bloqueos, bajamos el ritmo a lo minimo por prudencia
    if st.get("bloqueos", 0) >= 2 and etiqueta_plan == "ALTA":
        log("Venimos de {} bloqueos: bajo el ritmo por prudencia."
            .format(st["bloqueos"]))
        n_sondeos, espaciado = 1, 0

    log("{} {} | ritmo {} | {} sondeo(s) | buscando: {}".format(
        DIAS[now.weekday()], now.strftime("%H:%M"), etiqueta_plan,
        n_sondeos, etiqueta_busqueda()))

    # Espera aleatoria para no pegarle al servidor en el segundo exacto
    jitter = random.uniform(0, 12)
    time.sleep(jitter)

    cliente = DianClient()
    inicio = time.time()
    tramites = None
    error = None
    bloqueado = False

    for i in range(1, n_sondeos + 1):
        if time.time() - inicio > PRESUPUESTO_SEG:
            log("Se acabo el tiempo de la corrida, corto aqui.")
            break

        encontrados, err_local = None, None
        for intento in range(1, REINTENTOS + 1):
            try:
                encontrados = cliente.consultar_tramites(
                    TIPO_PERSONA, CATEGORIA, TIPO_ATENCION)
                break
            except Bloqueado as e:
                log("La DIAN nos corto: {}. Paro esta corrida.".format(e))
                bloqueado, err_local = True, e
                break
            except Exception as e:
                err_local = e
                log("Sondeo {} intento {}/{} fallo: {}".format(
                    i, intento, REINTENTOS, e))
                if intento < REINTENTOS:
                    time.sleep(4 * intento)

        if bloqueado:
            error = err_local
            break

        if encontrados is None:
            error = err_local
            break

        tramites = encontrados
        if FILTRO:
            tramites = [t for t in tramites if FILTRO.lower() in t.lower()]

        log("Sondeo {}/{}: {}".format(
            i, n_sondeos, tramites if tramites else "sin cupo"))

        if tramites:
            break   # ya encontramos, no hay para que seguir golpeando

        if i < n_sondeos:
            restante = PRESUPUESTO_SEG - (time.time() - inicio)
            if restante < espaciado + 10:
                log("No alcanza para otro sondeo, corto aqui.")
                break
            time.sleep(espaciado + random.uniform(-5, 5))

    # --- nos bloquearon ----------------------------------------------------
    if bloqueado:
        st["bloqueos"] = st.get("bloqueos", 0) + 1
        st["ultimo_error"] = str(error)[:300]
        log("Bloqueos acumulados: {}. Peticiones esta corrida: {}".format(
            st["bloqueos"], cliente.peticiones))
        if st["bloqueos"] >= 5 and not st.get("aviso_fallo_enviado"):
            enviar_whatsapp(
                "[Bot DIAN] La pagina de la DIAN me esta rechazando las consultas "
                "({} veces seguidas). Baje el ritmo automaticamente. "
                "Si sigue asi hay que revisar el bot.".format(st["bloqueos"])
            )
            st["aviso_fallo_enviado"] = True
        st["ultimo_plan"] = etiqueta_plan
        guardar_estado(st)
        return 0

    # --- la consulta fallo por otra razon ----------------------------------
    if tramites is None:
        st["fallos"] = st.get("fallos", 0) + 1
        st["ultimo_error"] = str(error)[:300]
        log("Consulta fallida. Fallos seguidos: {}".format(st["fallos"]))
        if st["fallos"] >= FALLOS_ANTES_DE_AVISAR and not st.get("aviso_fallo_enviado"):
            enviar_whatsapp(
                "[Bot DIAN] No he podido consultar la pagina en las ultimas {} "
                "revisiones. Puede que la DIAN haya cambiado algo o este caida.\n"
                "Ultimo error: {}".format(st["fallos"], st["ultimo_error"])
            )
            st["aviso_fallo_enviado"] = True
        st["ultimo_plan"] = etiqueta_plan
        guardar_estado(st)
        return 0

    # --- todo salio bien ---------------------------------------------------
    st["fallos"] = 0
    st["bloqueos"] = 0
    st["ultimo_error"] = None
    st["aviso_fallo_enviado"] = False
    st["ultimo_plan"] = etiqueta_plan

    if not tramites:
        if st.get("avisados"):
            log("Se cerro el cupo que ya habia avisado; limpio el estado.")
        st["avisados"] = []
    else:
        avisar(tramites, st)

    log("Peticiones a la DIAN esta corrida: {}".format(cliente.peticiones))
    guardar_estado(st)
    return 0


if __name__ == "__main__":
    sys.exit(main())
