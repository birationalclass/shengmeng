// Local development keeps its local API. Published pages use the Shanghai service.
export const RECORDS_API_URL=['localhost','127.0.0.1'].includes(location.hostname)
 ? 'http://127.0.0.1:8782'
 : 'https://birationalclass-d3fw2j6t76955af0-1493130792.ap-shanghai.app.tcloudbase.com/records';
export const RECORDS_CONFIG={provider:'http',url:RECORDS_API_URL};
